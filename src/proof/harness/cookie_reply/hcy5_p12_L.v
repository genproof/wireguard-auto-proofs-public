(* law cookie_reply, phase P12, segment L:
   s70: the ck_same loop over the cnodes but the target (v1 L: hcy4_p12_L.v + hcy4_p12_l_pure.v).
   St -> St over fixed values (hcy5_p12_defs.v). *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_l_pure.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers (prefix hcy5_p12_l_)                                            *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p12_l_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hcy5_p12_l_cookie_eqb_refl C : cookie_eqb C C = true.
Proof.
  unfold cookie_eqb. rewrite Int64.eq_true, !Bool.eqb_reflx, !hcy5_p12_l_eqb_refl. reflexivity.
Qed.

(* a cnode's fields *)
Definition hcy5_p12_l_cnode (c nd: val) (o: option cookie) (nx: val) : mpred :=
  (@malloc_token W Ews t_cnode5 c *
   @field_at W Ews t_cnode5 [StructField HY._n] nd c *
   hcy5_cs_rep o (offset_val 8 c) *
   @field_at W Ews t_cnode5 [StructField HY._next] nx c)%logic.

Lemma hcy5_p12_l_cns_cons l c nd o B :
  hcy5_cns l ((c, nd, o) :: B) =
  (!! (l = c) && (hcy5_p12_l_cnode c nd o (hcy5_chead B) * hcy5_cns (hcy5_chead B) B))%logic.
Proof. reflexivity. Qed.

Lemma hcy5_p12_l_wand_frame (A F B: mpred) : A * (F * (F -* B)) |-- F * (F -* (A * B)).
Proof.
  rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcy5_p12_l_wand_frame2 (A F B: mpred) : (F * (F -* B)) * A |-- F * (F -* (B * A)).
Proof.
  rewrite (sepcon_comm _ A). eapply derives_trans; [apply hcy5_p12_l_wand_frame |].
  rewrite (sepcon_comm A B). apply derives_refl.
Qed.

Lemma hcy5_p12_l_wand_eq (X F G: mpred) : X = (F * G)%logic -> X |-- F * (F -* X).
Proof.
  intros E. rewrite E at 1. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm, <- E. apply derives_refl.
Qed.

(* focus on a part X of the k-th cnode *)
Lemma hcy5_p12_l_focus (X: mpred) k l CL c0 nd o B :
  skipn k CL = (c0, nd, o) :: B ->
  hcy5_p12_l_cnode c0 nd o (hcy5_chead B) |-- X * (X -* hcy5_p12_l_cnode c0 nd o (hcy5_chead B)) ->
  hcy5_cns l CL |-- X * (X -* hcy5_cns l CL).
Proof.
  intros Hs HX. revert l CL Hs; induction k as [| k IH]; intros l CL Hs.
  - simpl in Hs. subst CL. rewrite hcy5_p12_l_cns_cons. Intros. subst l.
    rewrite (prop_true_andp (c0 = c0)) by reflexivity.
    sep_apply HX. apply hcy5_p12_l_wand_frame2.
  - destruct CL as [| [[c1 nd1] o1] CL']; simpl in Hs; [discriminate |].
    rewrite hcy5_p12_l_cns_cons. Intros. subst l.
    rewrite (prop_true_andp (c1 = c1)) by reflexivity.
    sep_apply (IH (hcy5_chead CL') CL' Hs). rewrite sepcon_comm. apply hcy5_p12_l_wand_frame.
Qed.

Lemma hcy5_p12_l_focus_body k l CL c0 nd C B :
  skipn k CL = (c0, nd, Some C) :: B ->
  hcy5_cns l CL |--
  (@field_at W Ews t_cnode5 [StructField HY._n] nd c0 *
   @data_at CKS Ews t_cksnap (cksnap_val C) (offset_val 8 c0)) *
  ((@field_at W Ews t_cnode5 [StructField HY._n] nd c0 *
    @data_at CKS Ews t_cksnap (cksnap_val C) (offset_val 8 c0)) -* hcy5_cns l CL).
Proof.
  intros Hs. apply (hcy5_p12_l_focus _ k l CL c0 nd (Some C) B Hs).
  apply hcy5_p12_l_wand_eq with (G := (@malloc_token W Ews t_cnode5 c0 *
    @field_at W Ews t_cnode5 [StructField HY._next] (hcy5_chead B) c0)%logic).
  unfold hcy5_p12_l_cnode, hcy5_cs_rep. apply pred_ext; cancel.
Qed.

Lemma hcy5_p12_l_focus_next k l CL c0 nd o B :
  skipn k CL = (c0, nd, o) :: B ->
  hcy5_cns l CL |--
  @field_at W Ews t_cnode5 [StructField HY._next] (hcy5_chead B) c0 *
  (@field_at W Ews t_cnode5 [StructField HY._next] (hcy5_chead B) c0 -* hcy5_cns l CL).
Proof.
  intros Hs. apply (hcy5_p12_l_focus _ k l CL c0 nd o B Hs).
  apply hcy5_p12_l_wand_eq with (G := (@malloc_token W Ews t_cnode5 c0 *
    @field_at W Ews t_cnode5 [StructField HY._n] nd c0 * hcy5_cs_rep o (offset_val 8 c0))%logic).
  unfold hcy5_p12_l_cnode. apply pred_ext; cancel.
Qed.

Lemma hcy5_p12_l_cns_vp l CL v :
  (v = nullval \/ In v (map (fun x => fst (fst x)) CL)) -> hcy5_cns l CL |-- valid_pointer v.
Proof.
  intros [-> | Hin]; [apply valid_pointer_null |].
  revert l; induction CL as [| [[c nd] o] CL IH]; intros l; [contradiction |].
  rewrite hcy5_p12_l_cns_cons. unfold hcy5_p12_l_cnode. Intros.
  destruct Hin as [Hv | Hin].
  - simpl in Hv. subst v.
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply field_at_valid_ptr0; auto. vm_compute. reflexivity.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hcy5_p12_l_cns_ptrs l CL : hcy5_cns l CL |-- !! Forall (fun x => isptr (fst (fst x))) CL.
Proof.
  revert l; induction CL as [| [[c nd] o] CL IH]; intros l.
  - simpl. entailer!.
  - rewrite hcy5_p12_l_cns_cons. unfold hcy5_p12_l_cnode. Intros.
    sep_apply (IH (hcy5_chead CL)). entailer!.
Qed.

(* lists *)
Lemma hcy5_p12_l_skipn_S {A: Type} (l: list A) k x B : skipn k l = x :: B -> skipn (S k) l = B.
Proof.
  revert l; induction k as [| k IH]; intros l Hs.
  - destruct l; simpl in *; [discriminate | inv Hs; reflexivity].
  - destruct l as [| y l]; simpl in *; [discriminate |]. apply IH. exact Hs.
Qed.

Lemma hcy5_p12_l_skipn_in {A: Type} (l: list A) k x : In x (skipn k l) -> In x l.
Proof.
  revert l; induction k as [| k IH]; intros l Hs; [exact Hs |].
  destruct l as [| y l]; simpl in *; [contradiction |]. right. apply IH. exact Hs.
Qed.

Lemma hcy5_p12_l_skipn_lt {A: Type} (l: list A) k x r : skipn k l = x :: r -> (k < length l)%nat.
Proof.
  revert l; induction k as [| k IH]; intros l Hs.
  - destruct l; simpl in *; [discriminate | lia].
  - destruct l as [| y l]; simpl in *; [discriminate |]. specialize (IH l Hs). lia.
Qed.

Lemma hcy5_p12_l_skipn_nil {A: Type} (l: list A) k : skipn k l = [] -> (length l <= k)%nat.
Proof.
  revert l; induction k as [| k IH]; intros l Hs.
  - destruct l; simpl in *; [lia | discriminate].
  - destruct l as [| y l]; simpl in *; [lia |]. specialize (IH l Hs). lia.
Qed.

Lemma hcy5_p12_l_chead_pn CL k :
  Forall (fun x => isptr (fst (fst x))) CL -> is_pointer_or_null (hcy5_chead (skipn k CL)).
Proof.
  intros HF. destruct (skipn k CL) as [| [[c nd] o] B] eqn:Hs; simpl; [reflexivity |].
  assert (Hin: In (c, nd, o) CL) by (apply (hcy5_p12_l_skipn_in CL k); rewrite Hs; left; reflexivity).
  rewrite Forall_forall in HF. specialize (HF _ Hin). simpl in HF. destruct c; try contradiction; exact I.
Qed.

Lemma hcy5_p12_l_chead_in CL k :
  hcy5_chead (skipn k CL) = nullval \/ In (hcy5_chead (skipn k CL)) (map (fun x => fst (fst x)) CL).
Proof.
  destruct (skipn k CL) as [| [[c nd] o] B] eqn:Hs; simpl; [left; reflexivity | right].
  apply (in_map (fun x => fst (fst x)) CL (c, nd, o)).
  apply (hcy5_p12_l_skipn_in CL k). rewrite Hs. left. reflexivity.
Qed.

Lemma hcy5_p12_l_cfind_in NS CL a :
  hcy5_cfind NS CL a = nullval \/ In (hcy5_cfind NS CL a) (map (fun x => fst (fst x)) CL).
Proof.
  induction CL as [| [[c nd] o] CL IH]; simpl; [left; reflexivity |].
  destruct (EqDec_val (hcy5_nodepeer NS nd) a); [right; left; reflexivity |].
  destruct IH as [IH | IH]; [left; exact IH | right; right; exact IH].
Qed.

Lemma hcy5_p12_l_tgt_in NS CL res :
  hcy5_tgt NS CL res = nullval \/ In (hcy5_tgt NS CL res) (map (fun x => fst (fst x)) CL).
Proof.
  destruct res as [[a P] |]; simpl; [apply hcy5_p12_l_cfind_in | left; reflexivity].
Qed.

(* ---- the field p of a node: focus with a wand (template hcy5_p9_BA1_node) ---- *)
#[local] Instance hcy5_p12_l_cce_HN : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

Lemma hcy5_p12_l_wand_frame3 (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcy5_p12_l_node1 (N: hnode4) nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
Proof.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

Lemma hcy5_p12_l_node h NS N v :
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
    + sep_apply (hcy5_p12_l_node1 N nx). cancel.
    + apply hcy5_p12_l_wand_frame3. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W Ews t_peer (hn_p N0) *
       (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hcy5_p12_l_wand_frame3. Exists nx. entailer!.
Qed.

(* ---- a peer's cookie: focus with a wand (template hcy5_p10_b_peer) ---- *)
Definition hcy5_p12_l_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Lemma hcy5_p12_l_peer_split sh a P :
  peer_rep sh a P = (cookie_rep sh (cookie_addr a) (p_cookie P) * hcy5_p12_l_prest sh a P)%logic.
Proof.
  unfold peer_rep, hcy5_p12_l_prest. apply pred_ext; entailer!; cancel.
Qed.

Lemma hcy5_p12_l_peer PS a sh P :
  In (a, sh, P) PS ->
  peers_rep PS |-- cookie_rep sh (cookie_addr a) (p_cookie P) * (cookie_rep sh (cookie_addr a) (p_cookie P) -* peers_rep PS).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  apply hcy5_p12_l_wand_eq with (G := (hcy5_p12_l_prest sh a P * iter_sepcon peer_item_rep l1 *
                                         iter_sepcon peer_item_rep l2)%logic).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  rewrite hcy5_p12_l_peer_split. apply pred_ext; cancel.
Qed.

Lemma hcy5_p12_l_pfc PS a sh P :
  In (a, sh, P) PS -> peers_rep PS |-- !! (@field_compatible Noise.CS t_peer [] a).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  unfold peer_rep at 1. entailer!.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p12_L_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE CM' honest now2 :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2 ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)
    hcy5_p12_s70
    (normal_ret_assert (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)).
Proof.
  intros HH Hinv.
  pose proof Hinv as (Hrep & Hlists & Hnp & HT & Hcl & Hsnap & Hcm & Hhon & Hnow).
  unfold hcy5_p12_St, hcy5_Delta, hcy5_p12_s70. simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  set (res := hcy5_res xaead_dec T PS CM' now2).
  set (NS' := hnodes_snapped4 T NS PS).
  freeze [0;1;2;3;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39] Fr.
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Lr) (SEPx (?F :: _)))) _ _ =>
  forward_loop (EX k: nat,
    PROPx [(k <= length CL)%nat]
    (LOCALx (temp HY._cn (hcy5_chead (skipn k CL)) :: Lr)
    (SEPx [F; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep (peers_after PS res);
           hcy5_cns (hcy5_chead CL) CL])))
  continue: (EX k: nat,
    PROPx [(k < length CL)%nat]
    (LOCALx (temp HY._cn (hcy5_chead (skipn k CL)) :: Lr)
    (SEPx [F; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep (peers_after PS res);
           hcy5_cns (hcy5_chead CL) CL])))
  break: (PROPx []
    (LOCALx (temp HY._cn nullval :: Lr)
    (SEPx [F; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep (peers_after PS res);
           hcy5_cns (hcy5_chead CL) CL])))
  end.
  { Exists 0%nat. entailer!. }
  { Intros k.
    assert_PROP (Forall (fun x => isptr (fst (fst x))) CL) as Hptrs.
    { sep_apply (hcy5_p12_l_cns_ptrs (hcy5_chead CL) CL). entailer!. }
    pose proof (hcy5_p12_l_chead_pn CL k Hptrs) as Hpn.
    assert (VP: hcy5_cns (hcy5_chead CL) CL |-- valid_pointer (hcy5_chead (skipn k CL)))
      by (apply hcy5_p12_l_cns_vp; apply hcy5_p12_l_chead_in).
    forward_if.
    - (* cn not NULL *)
      forward_if.
      + (* the test cn != target *)
        apply denote_tc_test_eq_split; apply sepcon_valid_pointer2;
          [exact VP | apply hcy5_p12_l_cns_vp; apply hcy5_p12_l_tgt_in].
      + (* cn != target: the CHECK *)
        destruct (skipn k CL) as [| [[c0 nd] o] B] eqn:Hsk; [simpl in H0; contradiction |].
        destruct (hcy5_p12_l_pick L (map ke_addr KE) T NS PS CL res k c0 nd o B Hlists Hcl Hsnap Hsk)
          as (N & a & P & HNin & HNa & HNp & HPin & Ho & Hres).
        specialize (Hres H1). subst o nd. fold NS' in HNin.
        change (hcy5_chead ((c0, hn_addr N, Some (p_cookie P)) :: B)) with c0 in *.
        sep_apply (hcy5_p12_l_focus_body k (hcy5_chead CL) CL c0 (hn_addr N) (p_cookie P) B Hsk). Intros.
        sep_apply (hcy5_p12_l_node (hcy5_head NS') NS' N a HNin HNp). Intros.
        assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfc.
        { sep_apply (hcy5_p12_l_pfc (peers_after PS res) a Ews P Hres). entailer!. }
        assert (Hpa: isptr a) by exact (field_compatible_isptr _ _ _ Hfc).
        sep_apply (hcy5_p12_l_peer (peers_after PS res) a Ews P Hres). Intros.
        match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
        * apply ENTAIL_refl.
        * forward.
          forward.
          forward_call (Ews, offset_val 8 c0, p_cookie P, Ews, cookie_addr a, p_cookie P).
          rewrite hcy5_p12_l_cookie_eqb_refl.
          forward_if.
          { exfalso. exact (Int.one_not_zero H2). }
          forward.
          entailer!.
        * forward. entailer!.
        * sep_apply (modus_ponens_wand (cookie_rep Ews (cookie_addr a) (p_cookie P))).
          sep_apply (modus_ponens_wand (@field_at W Ews t_hnode4 (DOT HY._p) a (hn_addr N))).
          sep_apply (modus_ponens_wand (@field_at W Ews t_cnode5 (DOT HY._n) (hn_addr N) c0 *
                                        @data_at CKS Ews t_cksnap (cksnap_val (p_cookie P)) (offset_val 8 c0))%logic).
          unfold POSTCONDITION, abbreviate. simpl_ret_assert.
          Exists k.
          pose proof (hcy5_p12_l_skipn_lt CL k _ _ Hsk).
          rewrite Hsk. entailer!.
      + (* cn = target: nothing *)
        forward.
        Exists k.
        destruct (skipn k CL) as [| [[c0 nd] o] B] eqn:Hsk; [simpl in H0; contradiction |].
        pose proof (hcy5_p12_l_skipn_lt CL k _ _ Hsk).
        entailer!.
    - (* cn = NULL: break *)
      forward.
      entailer!. }
  { (* cn = cn->next *)
    Intros k.
    assert_PROP (Forall (fun x => isptr (fst (fst x))) CL) as Hptrs.
    { sep_apply (hcy5_p12_l_cns_ptrs (hcy5_chead CL) CL). entailer!. }
    destruct (skipn k CL) as [| [[c0 nd] o] B] eqn:Hsk.
    { exfalso. pose proof (hcy5_p12_l_skipn_nil CL k Hsk). lia. }
    pose proof (hcy5_p12_l_skipn_S CL k _ _ Hsk) as HskS.
    pose proof (hcy5_p12_l_chead_pn CL (Datatypes.S k) Hptrs) as HpnS. rewrite HskS in HpnS.
    change (hcy5_chead ((c0, nd, o) :: B)) with c0.
    sep_apply (hcy5_p12_l_focus_next k (hcy5_chead CL) CL c0 nd o B Hsk). Intros.
    forward.
    sep_apply (modus_ponens_wand (@field_at W Ews t_cnode5 [StructField HY._next] (hcy5_chead B) c0)).
    Exists (Datatypes.S k). rewrite HskS. entailer!. }
  unfold POSTCONDITION, abbreviate. simpl_ret_assert. thaw Fr.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  subst res NS'. entailer!.
Qed.

End Seg.
