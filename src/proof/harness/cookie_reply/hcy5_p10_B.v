(* law cookie_reply, phase P10, segment B:
   statement 58: for (cn = cns; cn; cn = cn->next) ck_take(&cn->cs, &cn->n->p->latest_cookie).
*)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p10_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p10_b_pure.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---- the cnodes done so far: a segment from l to e ---- *)
Fixpoint hcy5_p10_b_seg (l e: val) (CL: list (val * val * option cookie)) : mpred :=
  match CL with
  | [] => !! (l = e) && emp
  | (c, nd, o) :: CL' =>
      !! (l = c) &&
      EX nx: val,
        (@malloc_token W Ews t_cnode5 c *
         @field_at W Ews t_cnode5 [StructField HY._n] nd c *
         hcy5_cs_rep o (offset_val 8 c) *
         @field_at W Ews t_cnode5 [StructField HY._next] nx c *
         hcy5_p10_b_seg nx e CL')
  end.

Lemma hcy5_p10_b_cns_cons l c nd o B :
  hcy5_cns l ((c, nd, o) :: B) =
  (!! (l = c) &&
   (@malloc_token W Ews t_cnode5 c *
    @field_at W Ews t_cnode5 [StructField HY._n] nd c *
    hcy5_cs_rep o (offset_val 8 c) *
    @field_at W Ews t_cnode5 [StructField HY._next] (hcy5_chead B) c *
    hcy5_cns (hcy5_chead B) B))%logic.
Proof. reflexivity. Qed.

Lemma hcy5_p10_b_cns_nil l : hcy5_cns l [] = (!! (l = nullval) && emp)%logic.
Proof. reflexivity. Qed.

Lemma hcy5_p10_b_cns_head l B : hcy5_cns l B |-- !! (l = hcy5_chead B).
Proof. destruct B as [| [[c nd] o] B]; simpl; entailer!. Qed.

Lemma hcy5_p10_b_cns_pn l B : hcy5_cns l B |-- !! is_pointer_or_null l.
Proof.
  destruct B as [| [[c nd] o] B]; simpl.
  - entailer!.
  - Intros. subst. entailer!.
Qed.

Lemma hcy5_p10_b_cns_tc F l B : F * hcy5_cns l B |-- denote_tc_test_eq l (Vlong Int64.zero).
Proof.
  destruct B as [| [[c nd] o] B]; simpl.
  - Intros. subst. entailer!.
  - Intros. subst. apply denote_tc_test_eq_split; [| apply valid_pointer_zero64; auto].
    apply sepcon_valid_pointer2.
    apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply field_at_valid_ptr0; auto. vm_compute. reflexivity.
Qed.

Lemma hcy5_p10_b_seg_snoc l e A c nd o nx :
  e = c ->
  hcy5_p10_b_seg l e A *
  (@malloc_token W Ews t_cnode5 c *
   @field_at W Ews t_cnode5 [StructField HY._n] nd c *
   hcy5_cs_rep o (offset_val 8 c) *
   @field_at W Ews t_cnode5 [StructField HY._next] nx c) |--
  hcy5_p10_b_seg l nx (A ++ [(c, nd, o)]).
Proof.
  intros He. revert l; induction A as [| [[c1 nd1] o1] A IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx1. Exists nx1. entailer!. sep_apply (IH nx1). cancel.
Qed.

Lemma hcy5_p10_b_seg_end l A : hcy5_p10_b_seg l nullval A |-- hcy5_cns l A.
Proof.
  revert l; induction A as [| [[c nd] o] A IH]; intros l; simpl.
  - entailer!.
  - Intros nx. sep_apply (IH nx). sep_apply (hcy5_p10_b_cns_head nx A). Intros. subst. entailer!.
Qed.

(* ---- the field p of a node: focus with a wand (template hcy5_p9_BA1_node) ---- *)
#[local] Instance hcy5_p10_b_cce_HN : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

Lemma hcy5_p10_b_wand_frame (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcy5_p10_b_node1 (N: hnode4) nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
Proof.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

Lemma hcy5_p10_b_node h NS N v :
  In N NS -> hn_p N = v ->
  hnodes_rep4 W h NS |--
  @field_at W Ews t_hnode4 (DOT HY._p) v (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HY._p) v (hn_addr N) -* hnodes_rep4 W h NS).
Proof.
  intros Hin <-. revert h. induction NS as [| N0 NS IH]; intros h; [contradiction |].
  destruct Hin as [-> | Hin].
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N) * @malloc_token W Ews t_peer (hn_p N) *
       hnodes_rep4 W nx NS *
       (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
         @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N))))%logic.
    + sep_apply (hcy5_p10_b_node1 N nx). cancel.
    + apply hcy5_p10_b_wand_frame. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W Ews t_peer (hn_p N0) *
       (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hcy5_p10_b_wand_frame. Exists nx. entailer!.
Qed.

(* ---- a peer's cookie: focus with a wand ---- *)
Definition hcy5_p10_b_prest (sh: share) (p: val) (P: peer) : mpred :=
  (!! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p))%logic.

Lemma hcy5_p10_b_peer_split sh a P :
  peer_rep sh a P = (cookie_rep sh (cookie_addr a) (p_cookie P) * hcy5_p10_b_prest sh a P)%logic.
Proof.
  unfold peer_rep, hcy5_p10_b_prest. apply pred_ext; entailer!; cancel.
Qed.

Lemma hcy5_p10_b_wand_eq (X F G: mpred) : X = (F * G)%logic -> X |-- F * (F -* X).
Proof.
  intros E. rewrite E at 1. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm, <- E. apply derives_refl.
Qed.

Lemma hcy5_p10_b_peer PS a sh P :
  In (a, sh, P) PS ->
  peers_rep PS |-- cookie_rep sh (cookie_addr a) (p_cookie P) * (cookie_rep sh (cookie_addr a) (p_cookie P) -* peers_rep PS).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  apply hcy5_p10_b_wand_eq with (G := (hcy5_p10_b_prest sh a P * iter_sepcon peer_item_rep l1 *
                                         iter_sepcon peer_item_rep l2)%logic).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  rewrite hcy5_p10_b_peer_split. apply pred_ext; cancel.
Qed.

Lemma hcy5_p10_b_pfc PS a sh P :
  In (a, sh, P) PS -> peers_rep PS |-- !! (@field_compatible Noise.CS t_peer [] a).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  unfold peer_rep at 1. entailer!.
Qed.

Lemma hcy5_p10_b_firstn_snoc {A: Type} (l: list A) k x r :
  skipn k l = x :: r -> firstn (S k) l = firstn k l ++ [x].
Proof.
  revert l; induction k as [| k IH]; intros l Hs.
  - destruct l; simpl in *; [discriminate | inv Hs; reflexivity].
  - destruct l as [| y l]; simpl in *; [discriminate |]. f_equal. apply IH. exact Hs.
Qed.

Lemma hcy5_p10_b_skipn_lt {A: Type} (l: list A) k x r : skipn k l = x :: r -> (k < length l)%nat.
Proof.
  revert l; induction k as [| k IH]; intros l Hs.
  - destruct l; simpl in *; [discriminate | lia].
  - destruct l as [| y l]; simpl in *; [discriminate |]. specialize (IH l Hs). lia.
Qed.

Lemma hcy5_p10_b_skipn_nil {A: Type} (l: list A) k : skipn k l = [] -> (length l <= k)%nat.
Proof. intros Hs. pose proof (length_skipn k l) as Hl. rewrite Hs in Hl. simpl in Hl. lia. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p10_B_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_p10_TA x25519 xaead_enc gv L FR) hcy5_p10_sB
    (overridePost (hcy5_p10_TB x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_p10_TA, hcy5_Delta, hcy5_R, hcy5_p10_sB. simplify_func_tycontext. abbreviate_semax.
  Intros R Sh m c rp Q nonce rr CK CM.
  Intros NS PS T np CL KE CM' honest.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  pose proof H0 as (Hpok & Hnp & Hnd1 & Hnd2 & Hpk).
  freeze [0;1;2;3;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39] Fr.
  forward.
  set (NS' := hnodes_snapped4 T NS PS).
  set (CLs := hcy5_p10_b_CLs CL PS).
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Lr) (SEPx (?F :: _)))) _ _ =>
  forward_loop (EX k: nat,
    PROPx [(k <= length CL)%nat]
    (LOCALx (temp HY._cn (hcy5_chead (skipn k CL)) :: Lr)
    (SEPx [F; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep PS;
          hcy5_p10_b_seg (hcy5_chead CL) (hcy5_chead (skipn k CL)) (firstn k CLs);
          hcy5_cns (hcy5_chead (skipn k CL)) (skipn k CL)])))
  continue: (EX k: nat, EX c0: val, EX nd: val, EX C: cookie,
    PROPx [skipn k CLs = (c0, nd, Some C) :: skipn (S k) CLs; length CLs = length CL]
    (LOCALx (temp HY._cn c0 :: Lr)
    (SEPx [F; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep PS;
          hcy5_p10_b_seg (hcy5_chead CL) c0 (firstn k CLs);
          @malloc_token W Ews t_cnode5 c0;
          @field_at W Ews t_cnode5 [StructField HY._n] nd c0;
          hcy5_cs_rep (Some C) (offset_val 8 c0);
          @field_at W Ews t_cnode5 [StructField HY._next] (hcy5_chead (skipn (S k) CL)) c0;
          hcy5_cns (hcy5_chead (skipn (S k) CL)) (skipn (S k) CL)])))
  break: (PROPx []
    (LOCALx (temp HY._cn nullval :: Lr)
    (SEPx [F; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep PS; hcy5_cns (hcy5_chead CL) CLs])))
  end.
  { Exists 0%nat. entailer!. cbn [skipn firstn hcy5_p10_b_seg]. entailer!. }
  { Intros k.
    assert_PROP (is_pointer_or_null (hcy5_chead (skipn k CL))) as Hpn.
    { sep_apply (hcy5_p10_b_cns_pn (hcy5_chead (skipn k CL)) (skipn k CL)). entailer!. }
    forward_if.
    - (* the test of cn *)
      apply hcy5_p10_b_cns_tc.
    - (* cn not NULL: the cnode k *)
      destruct (skipn k CL) as [| [[c0 nd] o] B] eqn:Hsk; [simpl in H8; contradiction |].
      destruct (hcy5_p10_b_pick T NS PS CL k c0 nd o B Hnp H3 H4 Hsk)
        as (-> & -> & N & a & sh & P & HNin & HNa & HNp & HPin & HCs).
      fold NS' CLs in HNin, HCs.
      assert (Hsh: sh = Ews) by (rewrite Forall_forall in Hpok; apply (Hpok _ HPin)).
      subst sh nd.
      assert (Hc: hcy5_chead ((c0, hn_addr N, None) :: skipn (Datatypes.S k) CL) = c0) by reflexivity.
      rewrite Hc. rewrite hcy5_p10_b_cns_cons. Intros.
      sep_apply (hcy5_p10_b_node (hcy5_head NS') NS' N a HNin HNp). Intros.
      assert_PROP (isptr (hn_addr N)) as HNptr.
      { entailer!. }
      assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfc.
      { sep_apply (hcy5_p10_b_pfc PS a Ews P HPin). entailer!. }
      assert (Hpa: isptr a) by exact (field_compatible_isptr _ _ _ Hfc).
      forward.
      forward.
      sep_apply (modus_ponens_wand (@field_at W Ews t_hnode4 (DOT HY._p) a (hn_addr N))).
      sep_apply (hcy5_p10_b_peer PS a Ews P HPin). Intros.
      unfold hcy5_cs_rep.
      forward_call (Ews, offset_val 8 c0, Ews, cookie_addr a, p_cookie P).
      sep_apply (modus_ponens_wand (cookie_rep Ews (cookie_addr a) (p_cookie P))).
      Exists k c0 (hn_addr N) (p_cookie P).
      destruct (hcy5_p10_b_end NS PS CL Hnp H3) as (_ & _ & _ & Hl1). fold CLs in Hl1.
      unfold hcy5_cs_rep. entailer!.
    - (* cn NULL: break *)
      assert_PROP (skipn k CL = []) as Hsk.
      { destruct (skipn k CL) as [| [[c0 nd] o] B] eqn:E; [entailer! |].
        rewrite hcy5_p10_b_cns_cons. Intros. subst. entailer!. }
      pose proof (hcy5_p10_b_skipn_nil CL k Hsk) as Hk.
      destruct (hcy5_p10_b_end NS PS CL Hnp H3) as (_ & _ & _ & Hl1). fold CLs in Hl1.
      assert (Hn: hcy5_chead (@nil (val * val * option cookie)) = nullval) by reflexivity.
      rewrite Hsk, Hn.
      forward.
      rewrite firstn_all2 by lia.
      sep_apply (hcy5_p10_b_seg_end (hcy5_chead CL) CLs).
      rewrite hcy5_p10_b_cns_nil. entailer!. }
  { Intros k c0 nd C.
    match goal with Hs: skipn k CLs = _ |- _ => rename Hs into HCs end.
    match goal with Hs: length CLs = length CL |- _ => rename Hs into Hl1 end.
    assert_PROP (is_pointer_or_null (hcy5_chead (skipn (Datatypes.S k) CL))) as Hpn.
    { sep_apply (hcy5_p10_b_cns_pn (hcy5_chead (skipn (Datatypes.S k) CL)) (skipn (Datatypes.S k) CL)). entailer!. }
    forward.
    Exists (Datatypes.S k).
    pose proof (hcy5_p10_b_skipn_lt CLs k _ _ HCs) as Hlt.
    rewrite (hcy5_p10_b_firstn_snoc CLs k _ _ HCs).
    entailer!.
    sep_apply (hcy5_p10_b_seg_snoc (hcy5_chead CL) c0 (firstn k CLs) c0 nd (Some C)
                 (hcy5_chead (skipn (Datatypes.S k) CL)) eq_refl).
    cancel. }
  unfold POSTCONDITION, abbreviate. simpl_ret_assert.
  thaw Fr. unfold hcy5_p10_TB.
  destruct (hcy5_p10_b_end NS PS CL Hnp H3) as (Hn1 & Hs1 & Hh1 & Hl1). fold CLs in Hn1, Hs1, Hh1, Hl1.
  Exists R Sh m c rp Q nonce rr CK CM. Exists NS PS T np CLs KE CM' honest.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  rewrite Hh1. entailer!.
  apply derives_refl.
Qed.

End Seg.
