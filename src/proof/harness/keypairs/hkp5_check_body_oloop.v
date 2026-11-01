(* law keypairs: the others loop OLOOP from ONODE (a hypothesis).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

#[local] Instance hkc5_ol_cceK : change_composite_env CKS W_keypairs.
Proof. make_cs_preserve CKS W_keypairs. Defined.

(* the processed prefix of the others list: a segment from l to e *)
Fixpoint hkc5_ol_seg (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token W_keypairs Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l *
        @malloc_token W_keypairs Ews t_peer (hn_p N) *
        hkc5_ol_seg nx e NS'
  end.

Lemma hkc5_ol_seg_app l e NS1 NS2 :
  hkc5_ol_seg l e NS1 * hnodes_rep4 W_keypairs e NS2 |-- hnodes_rep4 W_keypairs l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [| N NS1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hkc5_ol_seg_snoc l e N nx NS1 : e = hn_addr N ->
  hkc5_ol_seg l e NS1 *
  (@malloc_token W_keypairs Ews t_hnode4 e *
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W_keypairs Ews t_peer (hn_p N)) |--
  hkc5_ol_seg l nx (NS1 ++ [N]).
Proof.
  intros He. revert l; induction NS1 as [| M NS1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx'. Exists nx'. entailer!. sep_apply (IH nx'). cancel.
Qed.

Lemma hkc5_ol_vp l NS : hnodes_rep4 W_keypairs l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hkc5_ol_pn l NS : hnodes_rep4 W_keypairs l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => apply field_compatible_isptr in Hf end.
    destruct (hn_addr N); try contradiction; exact I.
Qed.

#[local] Hint Resolve hkc5_ol_vp : valid_pointer.

Lemma hkc5_ol_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W_keypairs Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W_keypairs _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

(* the node's value as ONE constant at W *)
Definition hkc5_ol_nv (N: hnode4) (nx: val) : @reptype W_keypairs t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hkc5_ol_node_nv N nx l :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l =
  @data_at W_keypairs Ews t_hnode4 (hkc5_ol_nv N nx) l.
Proof. unfold hkc5_ol_nv. apply hkc5_ol_node_W. Qed.

(* the peers: the i-th and the others *)
Lemma hkc5_ol_peers_split PS i : 0 <= i < Zlength PS ->
  peers_rep PS = (peer_item_rep (Znth i PS) * peers_rep (hkc5_rest PS i))%logic.
Proof.
  intros Hi. unfold hkc5_rest, peers_rep.
  rewrite <- (sublist_same 0 (Zlength PS) PS) at 1 by auto.
  rewrite (sublist_split 0 i (Zlength PS)) by lia.
  rewrite (sublist_split i (i + 1) (Zlength PS)) by lia.
  rewrite sublist_len_1 by lia.
  rewrite !iter_sepcon_app. simpl iter_sepcon. rewrite sepcon_emp.
  rewrite <- !sepcon_assoc. f_equal. rewrite (sepcon_comm (iter_sepcon _ _)). reflexivity.
Qed.

Lemma hkc5_ol_vobjs_cons rest VO :
  vobjs W_keypairs (VPeers rest :: VO) = (peers_rep rest * vobjs W_keypairs VO)%logic.
Proof. reflexivity. Qed.

(* the counter *)
Lemma hkc5_ol_oh_snoc T PS i : 0 <= i < Zlength PS ->
  hkc5_oh T (sublist 0 (i + 1) PS) =
  hkc5_oh T (sublist 0 i PS) + (if vin (hs_addr (peer_addr4 (Znth i PS))) (t_L T) then 1 else 0).
Proof.
  intros Hi. unfold hkc5_oh.
  rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite filter_app, Zlength_app. cbn [filter].
  destruct (vin _ _); reflexivity.
Qed.

Lemma hkc5_ol_use {Espec: OracleKind} {cs: compspecs} Delta P Q c (R: ret_assert) :
  ENTAIL Delta, Q |-- RA_normal R -> @semax cs Espec Delta P c (overridePost Q R) -> @semax cs Espec Delta P c R.
Proof.
  intros HQ HS. eapply semax_post; [ | | | | exact HS]; destruct R; unfold overridePost; cbn;
  auto; intros; apply andp_left2; apply derives_refl.
Qed.

Lemma hkc5_oloop_ok : hkc5_oloop_stmt.
Proof.
  intros HON Espec F T hd NS PS VO n FR R HL HOK.
  rewrite hkc5_oloop_eq. unfold hkc5_PO, hkc5_lv.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  assert_PROP (is_pointer_or_null hd) as Hpn by (sep_apply (hkc5_ol_pn hd NS); entailer!).
  forward.
  forward_loop
    (EX i: Z, EX o: val,
     PROP (0 <= i <= Zlength NS)
     LOCAL (temp KC._o o; temp KC._hashed (Vlong (Int64.repr (n + hkc5_oh T (sublist 0 i PS))));
            temp KC._p (f_p F); temp KC._t (f_t F); temp KC._w (f_w F); gvars (f_gv F))
     SEP (data_at Ews (tptr t_hnode4) hd (f_gv F KC._others); hkc5_ol_seg hd o (sublist 0 i NS);
          hnodes_rep4 W_keypairs o (sublist i (Zlength NS) NS); peers_rep PS;
          itable Tsh (f_t F) T; vobjs W_keypairs VO; FR))
  continue:
    (EX i: Z, EX nx: val,
     PROP (0 <= i < Zlength NS)
     LOCAL (temp KC._o (hn_addr (Znth i NS));
            temp KC._hashed (Vlong (Int64.repr (n + hkc5_oh T (sublist 0 (i + 1) PS))));
            temp KC._p (f_p F); temp KC._t (f_t F); temp KC._w (f_w F); gvars (f_gv F))
     SEP (data_at Ews (tptr t_hnode4) hd (f_gv F KC._others); hkc5_ol_seg hd (hn_addr (Znth i NS)) (sublist 0 i NS);
          @malloc_token W_keypairs Ews t_hnode4 (hn_addr (Znth i NS));
          @data_at CKS Ews t_hnode4 (hn_p (Znth i NS), (hn_snap (Znth i NS), (hn_refs (Znth i NS),
                                     (hn_rest (Znth i NS), nx)))) (hn_addr (Znth i NS));
          @malloc_token W_keypairs Ews t_peer (hn_p (Znth i NS));
          hnodes_rep4 W_keypairs nx (sublist (i + 1) (Zlength NS) NS); peers_rep PS;
          itable Tsh (f_t F) T; vobjs W_keypairs VO; FR))
  break:
    (PROP ()
     LOCAL (temp KC._hashed (Vlong (Int64.repr (n + hkc5_oh T PS)));
            temp KC._p (f_p F); temp KC._t (f_t F); temp KC._w (f_w F); gvars (f_gv F))
     SEP (data_at Ews (tptr t_hnode4) hd (f_gv F KC._others); hnodes_rep4 W_keypairs hd NS; peers_rep PS;
          itable Tsh (f_t F) T; vobjs W_keypairs VO; FR)).
  - (* entry *)
    Exists 0 hd. rewrite sublist_nil, (sublist_same 0 (Zlength NS) NS) by lia.
    change (hkc5_oh T []) with 0. rewrite Z.add_0_r. simpl hkc5_ol_seg. entailer!.
  - (* body *)
    Intros i o.
    assert (i = Zlength NS \/ i < Zlength NS) as [-> | Hi] by lia.
    + rewrite sublist_nil. simpl hnodes_rep4. Intros. subst o.
      forward_if; [contradiction |].
      forward.
      rewrite (sublist_same 0 (Zlength NS) NS), HL, (sublist_same 0 (Zlength PS) PS) by lia.
      assert (hkc5_ol_seg hd nullval NS |-- hnodes_rep4 W_keypairs hd NS) as Hs.
      { pose proof (hkc5_ol_seg_app hd nullval NS []) as Ha. rewrite app_nil_r in Ha.
        eapply derives_trans; [| exact Ha]. simpl hnodes_rep4. entailer!. }
      sep_apply Hs. entailer!.
    + rewrite (sublist_next i (Zlength NS) NS) by lia. cbn [hnodes_rep4]. Intros nx. subst o.
      assert_PROP (isptr (hn_addr (Znth i NS))) as Hptr.
      { entailer!. match goal with Hf: field_compatible t_hnode4 [] _ |- _ => apply field_compatible_isptr in Hf end.
        auto. }
      forward_if.
      * (* the node *)
        pose proof (HOK i ltac:(lia)) as Hok.
        set (FR' := (data_at Ews (tptr t_hnode4) hd (f_gv F KC._others) *
                     hkc5_ol_seg hd (hn_addr (Znth i NS)) (sublist 0 i NS) *
                     @malloc_token W_keypairs Ews t_hnode4 (hn_addr (Znth i NS)) *
                     @malloc_token W_keypairs Ews t_peer (hn_p (Znth i NS)) *
                     hnodes_rep4 W_keypairs nx (sublist (i + 1) (Zlength NS) NS) * FR)%logic).
        rewrite (hkc5_ol_peers_split PS i) by lia.
        pose proof (hkc5_ol_oh_snoc T PS i ltac:(lia)) as Hsn.
        destruct (Znth i PS) as [[q sh] Q] eqn:EP. cbn [peer_item_rep peer_addr4] in *.
        eapply hkc5_ol_use;
          [ | eapply semax_pre;
              [ | apply (HON Espec F T (Znth i NS) nx q sh Q (VPeers (hkc5_rest PS i) :: VO)
                         (n + hkc5_oh T (sublist 0 i PS)) FR'); exact Hok ] ].
        2: { unfold hkc5_PON, hkc5_lv, FR'. rewrite hkc5_ol_vobjs_cons. entailer!. }
        unfold POSTCONDITION, abbreviate. cbn [RA_normal loop1_ret_assert].
        Exists i nx. rewrite Hsn, Z.add_assoc.
        unfold hkc5_PON, hkc5_lv, FR'. rewrite hkc5_ol_vobjs_cons.
        rewrite (hkc5_ol_peers_split PS i), EP by lia. cbn [peer_item_rep]. entailer!.
      * exfalso. destruct (Znth i NS) as [a b c d e]; cbn in H0, Hptr; subst a; exact Hptr.
  - (* o = o->next *)
    Intros i nx.
    rewrite hkc5_ol_node_nv.
    assert_PROP (is_pointer_or_null nx) as Hnx
      by (sep_apply (hkc5_ol_pn nx (sublist (i + 1) (Zlength NS) NS)); entailer!).
    forward.
    Exists (i + 1) nx. rewrite <- hkc5_ol_node_nv.
    sep_apply (hkc5_ol_seg_snoc hd (hn_addr (Znth i NS)) (Znth i NS) nx (sublist 0 i NS) eq_refl).
    rewrite (sublist_split 0 i (i + 1) NS) by lia. rewrite (sublist_len_1 i NS) by lia.
    entailer!.
  - (* break *)
    unfold POSTCONDITION, abbreviate. cbn [RA_normal]. entailer!.
Qed.
