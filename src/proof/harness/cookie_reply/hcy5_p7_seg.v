(* law cookie_reply, phase P7: the loop body's segments, stated at hcy5_Delta (applied before simplify_func_tycontext):
   - brk: if (!it) break (Inv -> K false, or the exit to S7);
   - A: peer_randomize_rest(it->p) (K false -> K true);
   - B: if (nondet_u8() % 4 != 0) wg_index_hashtable_insert(&ita, &it->p->handshake.entry) (K true -> K true);
   - C: cn = malloc(sizeof *cn); if (cn == NULL) return 0; cn->n = it; cn->next = cns; cns = cn (K true -> Cont);
   - incr: it = it->next (Cont -> Inv). *)
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
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

#[local] Hint Resolve hcy5_p7_vp : valid_pointer.

(* A: peer_randomize_rest(it->p) *)
Lemma hcy5_p7_segA_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec
  gv L FR R Q m c rp rr CK CM np NS PS Rt :
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p7_K x25519 gv L FR R Q m c rp rr CK CM np NS PS false)
    hcy5_p7_A
    (overridePost (hcy5_p7_K x25519 gv L FR R Q m c rp rr CK CM np NS PS true) Rt).
Proof.
  unfold hcy5_Delta, hcy5_p7_K, hcy5_p7_A. simplify_func_tycontext. abbreviate_semax.
  Intros NS1 N NS2 PS1 PS1'. Intros P P' PS2 T' S'. Intros CL nx.
  cbn beta iota in *. subst P'.
  unfold hcy5_p7_lc, hcy5_lvars; cbn [app].
  assert_PROP (malloc_compatible (sizeof t_peer) (hn_p N)) as Hmc. { entailer!. }
  assert (Hpp: isptr (hn_p N)) by (unfold malloc_compatible in Hmc; destruct (hn_p N); try contradiction; simpl; auto).
  unfold hcy5_p7_nP. forward. fold (hcy5_p7_nP N).
  forward_call (Ews, hn_p N, P).
  Intros vret.
  destruct vret as [[[[[[dead lsh] valid] birth] ck] sent] mac1]. cbn [fst snd] in *.
  destruct Rt; cbn beta iota.
  Exists NS1 N NS2 PS1 PS1'. Exists P (p_rest_randomized P dead lsh valid birth ck sent mac1) PS2 T' S'.
  Exists CL nx.
  unfold hcy5_p7_lc, hcy5_lvars; cbn [app].
  cbn beta iota.
  entailer!.
  split; [reflexivity | split; [reflexivity |]].
  exists dead, lsh, valid, birth, ck, sent, mac1. reflexivity.
Qed.

(* B: if (nondet_u8() % 4 != 0) wg_index_hashtable_insert(&ita, &it->p->handshake.entry) *)
Lemma hcy5_p7_segB_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec
  gv L FR R Q m c rp rr CK CM np NS PS Rt :
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p7_K x25519 gv L FR R Q m c rp rr CK CM np NS PS true)
    hcy5_p7_B
    (overridePost (hcy5_p7_K x25519 gv L FR R Q m c rp rr CK CM np NS PS true) Rt).
Proof.
  unfold hcy5_Delta, hcy5_p7_K, hcy5_p7_B. simplify_func_tycontext. abbreviate_semax.
  Intros NS1 N NS2 PS1 PS1'. Intros P P' PS2 T' S'. Intros CL nx.
  cbn beta iota in *.
  unfold hcy5_p7_lc, hcy5_lvars; cbn [app].
  assert_PROP (malloc_compatible (sizeof t_peer) (hn_p N)) as Hmc. { entailer!. }
  assert (Hpp: isptr (hn_p N)) by (unfold malloc_compatible in Hmc; destruct (hn_p N); try contradiction; simpl; auto).
  assert (Hin: In (hn_p N) (map peer_addr4 PS)).
  { match goal with Hq: PS = _ |- _ => rewrite Hq end.
    rewrite map_app. apply in_or_app. right. left. reflexivity. }
  forward_call tt. Intros b5.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Lc (SEPx ?Rs))) _ _ =>
    let G := eval pattern T', S' in Rs in
    match G with ?G' T' S' =>
      forward_if (EX T'': tstate, EX S'': shim,
                  PROPx (hcy5_T_ok PS [] T'' :: Pr) (LOCALx Lc (SEPx (G' T'' S'')))) end end.
  - apply prop_right. intros [_ Hc]. apply (f_equal Int.signed) in Hc.
    rewrite Int.signed_repr in Hc by rep_lia. rewrite Int.signed_mone in Hc. lia.
  - unfold hcy5_p7_nP. forward. fold (hcy5_p7_nP N).
    assert_PROP (itable_wf T') as Hwf. { unfold itable. entailer!. }
    forward_call (gv, S', hcy5_w0, Tsh, l_ita L, T', hs_addr (hn_p N), @None (share * entry)).
    { cbn [raw_rep]. cancel. }
    { cbn [raw_ok]. eapply hcy5_p7_in; eauto. }
    Intros idx. cbn [raw_add] in *.
    Exists (t_insert T' (hs_addr (hn_p N)) idx) (shim_u32 S' idx).
    entailer!.
    eapply hcy5_p7_insert; eauto.
  - forward. Exists T' S'. entailer!.
  - Intros T'' S''.
    destruct Rt; cbn beta iota.
    Exists NS1 N NS2 PS1 PS1'. Exists P P' PS2 T'' S''. Exists CL nx.
    unfold hcy5_p7_lc, hcy5_lvars; cbn [app].
    cbn beta iota.
    entailer!.
Qed.

(* C: cn = malloc(sizeof *cn); if (cn == NULL) return 0; cn->n = it; cn->next = cns; cns = cn *)
Lemma hcy5_p7_segC_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec
  gv L FR R Q m c rp nonce rr CK CM np NS PS :
  hcy5_closeH -> hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p7_K x25519 gv L FR R Q m c rp rr CK CM np NS PS true)
    hcy5_p7_C
    (loop1_ret_assert (hcy5_p7_Cont x25519 gv L FR R Q m c rp rr CK CM np NS PS)
       (overridePost (hcy5_S7 x25519 xaead_enc gv L FR) hcy5_p7_Rf)).
Proof.
  intros HC HR.
  unfold hcy5_Delta, hcy5_p7_K, hcy5_p7_C, hcy5_p7_Rf. simplify_func_tycontext. abbreviate_semax.
  Intros NS1 N NS2 PS1 PS1'. Intros P P' PS2 T' S'. Intros CL nx.
  cbn beta iota in *.
  unfold hcy5_p7_lc, hcy5_lvars; cbn [app].
  forward_call (t_cnode5, gv).
  Intros cn.
  destruct (eq_dec cn nullval) as [Ecn | Ecn].
  - (* NULL: return 0 *)
    Intros. subst cn.
    forward_if.
    + forward.
      match goal with |- context [hcy5_p7_F _ _ _ _ _ _ _ _ _ _ _ _ ?ns ?ps] =>
        eapply derives_trans; [| apply (hcy5_p7_frame x25519 xaead_enc gv L FR R Q m c rp nonce rr CK CM
                                          ns ps T'); auto] end.
      cancel.
    + contradiction.
  - Intros.
    forward_if.
    + contradiction.
    + sep_apply (hcy5_p7_cn_split Ews cn).
      Intros.
      forward. forward. forward.
      assert_PROP (~ In cn (map (fun x => fst (fst x)) CL)) as Hfresh.
      { sep_apply (hcy5_p7_cns_fresh (hcy5_chead CL) CL (hcy5_chead CL) cn). entailer!. }
      unfold hcy5_p7_Cont.
      Exists NS1 N NS2 PS1 PS1'. Exists (hn_p N, Ews, P) (hn_p N, Ews, P') PS2 T' S'.
      Exists ((cn, hn_addr N, @None cookie) :: CL) nx.
      unfold hcy5_p7_lc, hcy5_lvars; cbn [app hcy5_cns hcy5_chead hcy5_cs_rep peer_item_rep].
      entailer!.
      split; [apply hcy5_p7_cl_push; auto | constructor; [reflexivity | auto]].
Qed.

Lemma hcy5_p7_node_join N nx :
  hcy5_p7_nP N * hcy5_p7_nS N * hcy5_p7_nX N nx |--
  @data_at CKS Ews t_hnode4 (hcy5_p7_nv N nx) (hn_addr N).
Proof. rewrite hcy5_p7_node_split. apply derives_refl. Qed.

(* if (!it) break: a node (K false) or the end of the list (S7) *)
Lemma hcy5_p7_brk_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec
  gv L FR R Q m c rp nonce rr CK CM np NS PS :
  hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM ->
  hcy5_lists_ok L [] NS PS -> hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p7_Inv x25519 gv L FR R Q m c rp rr CK CM np NS PS)
    hcy5_p7_brk
    (overridePost (hcy5_p7_K x25519 gv L FR R Q m c rp rr CK CM np NS PS false)
       (loop1_ret_assert (hcy5_p7_Cont x25519 gv L FR R Q m c rp rr CK CM np NS PS)
          (overridePost (hcy5_S7 x25519 xaead_enc gv L FR) hcy5_p7_Rf))).
Proof.
  intros HR HL HN.
  unfold hcy5_Delta, hcy5_p7_Inv, hcy5_p7_brk. simplify_func_tycontext. abbreviate_semax.
  Intros NS1 NS2 PS1 PS1' PS2. Intros T' S' CL it.
  unfold hcy5_p7_lc, hcy5_lvars; cbn [app].
  forward_if.
  - (* a node *)
    destruct NS2 as [| N NS2']; [simpl hnodes_rep4; Intros; subst it; contradiction |].
    destruct PS2 as [| x PS2']; [unfold hnodes_peers4 in *; discriminate |].
    match goal with Hp: hnodes_peers4 (N :: NS2') (x :: PS2') |- _ =>
      unfold hnodes_peers4 in Hp; cbn in Hp; injection Hp as Hpx Hnp' end.
    simpl hnodes_rep4. Intros nx. subst it.
    change (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) with (hcy5_p7_nv N nx).
    rewrite hcy5_p7_node_split.
    destruct x as [[a sh] P]. cbn in Hpx. subst a.
    change (peers_rep ((hn_p N, sh, P) :: PS2')) with (peer_rep sh (hn_p N) P * peers_rep PS2')%logic.
    assert (Hsh: sh = Ews).
    { destruct HL as (Hpok & _). rewrite Forall_forall in Hpok.
      destruct (Hpok (hn_p N, sh, P)) as [-> _]; [| reflexivity].
      match goal with Hq: PS = _ |- _ => rewrite Hq end.
      apply in_or_app; right; left; reflexivity. }
    subst sh.
    Intros.
    forward.
    unfold hcy5_p7_Rf, frame_ret_assert, loop1_ret_assert, function_body_ret_assert; cbn beta iota.
    unfold hcy5_p7_K.
    Exists NS1 N NS2' PS1 PS1'. Exists P P PS2' T' S'. Exists CL nx.
    unfold hcy5_p7_lc, hcy5_lvars; cbn [app]. cbn beta iota.
    entailer!.
  - (* the end of the list: S7 *)
    forward. subst it.
    destruct NS2 as [| N NS2'].
    2: { simpl hnodes_rep4. Intros nx.
         assert_PROP (isptr (hn_addr N)) as Hf. { entailer!. }
         match goal with Hq: nullval = hn_addr N |- _ => rewrite <- Hq in Hf end. contradiction. }
    destruct PS2 as [| x PS2']; [| unfold hnodes_peers4 in *; discriminate].
    rewrite !app_nil_r in *. subst NS PS.
    sep_apply (hcy5_p7_seg_app (hcy5_head NS1) nullval NS1 []). rewrite app_nil_r.
    assert (Ha: map peer_addr4 PS1' = map peer_addr4 PS1) by (apply hcy5_p7_addrs; auto).
    unfold hcy5_S7. Exists R S' m c rp Q nonce rr. Exists CK CM NS1 PS1' T' np CL.
    unfold hcy5_p7_F, hcy5_p7_Fl, hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0,
      hcy5_globs, hcy5_lvars; cbn [app fold_right_sepcon].
    rewrite (hcy5_p7_phead PS1 PS1' Ha).
    entailer!.
    split; [eapply hcy5_p7_lists; eauto |].
    split; [eapply hcy5_p7_np; eauto | eapply hcy5_p7_Tok; eauto].
Qed.

(* it = it->next *)
Lemma hcy5_p7_incr_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec
  gv L FR R Q m c rp rr CK CM np NS PS :
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p7_Cont x25519 gv L FR R Q m c rp rr CK CM np NS PS)
    hcy5_p7_incr
    (loop2_ret_assert (hcy5_p7_Inv x25519 gv L FR R Q m c rp rr CK CM np NS PS)
       (overridePost (hcy5_S7 x25519 xaead_enc gv L FR) hcy5_p7_Rf)).
Proof.
  unfold hcy5_Delta, hcy5_p7_Cont, hcy5_p7_incr. simplify_func_tycontext. abbreviate_semax.
  Intros NS1 N NS2 PS1 PS1'. Intros x y PS2 T' S'. Intros CL nx.
  unfold hcy5_p7_lc, hcy5_lvars; cbn [app].
  assert_PROP (is_pointer_or_null nx) as Hnx. { sep_apply (hcy5_p7_pn nx NS2). entailer!. }
  unfold hcy5_p7_nX.
  forward.
  fold (hcy5_p7_nX N nx).
  sep_apply (hcy5_p7_node_join N nx).
  sep_apply (hcy5_p7_seg_snoc (hcy5_head NS) (hn_addr N) N nx NS1 eq_refl).
  unfold hcy5_p7_Rf, frame_ret_assert, loop2_ret_assert, function_body_ret_assert; cbn beta iota.
  unfold hcy5_p7_Inv.
  Exists (NS1 ++ [N]) NS2 (PS1 ++ [x]) (PS1' ++ [y]) PS2. Exists T' S' CL nx.
  unfold hcy5_p7_lc, hcy5_lvars; cbn [app].
  rewrite hcy5_p7_peers_snoc.
  entailer!.
  split; [rewrite <- app_assoc; reflexivity |]. split; [rewrite <- app_assoc; reflexivity |].
  apply Forall2_app; [assumption | constructor; [assumption | constructor]].
Qed.

(* the body = brk; A; B; C *)
Lemma hcy5_p7_body_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec
  gv L FR R Q m c rp nonce rr CK CM np NS PS :
  hcy5_closeH -> hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM ->
  hcy5_lists_ok L [] NS PS -> hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p7_Inv x25519 gv L FR R Q m c rp rr CK CM np NS PS)
    hcy5_p7_body
    (loop1_ret_assert (hcy5_p7_Cont x25519 gv L FR R Q m c rp rr CK CM np NS PS)
       (overridePost (hcy5_S7 x25519 xaead_enc gv L FR) hcy5_p7_Rf)).
Proof.
  intros HC HR HL HN.
  rewrite hcy5_p7_body_eq.
  eapply semax_seq; [apply (hcy5_p7_brk_ok x25519 aead_enc aead_dec xaead_enc xaead_dec
                              gv L FR R Q m c rp nonce rr CK CM np NS PS); auto |].
  eapply semax_seq; [apply hcy5_p7_segA_ok |].
  eapply semax_seq; [apply hcy5_p7_segB_ok |].
  apply (hcy5_p7_segC_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R Q m c rp nonce rr CK CM np NS PS);
    auto.
Qed.
