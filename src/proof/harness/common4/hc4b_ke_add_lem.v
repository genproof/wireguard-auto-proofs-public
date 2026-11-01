(* pure model facts of kents_add's draws and
   separation facts used by the main proof (peer list, index table pool, harness node list). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf.
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf2.
Require Import WgNoise.proof.harness.common4.hc4b_ke_add_defs.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

(* ------------------------------------------------------------------------------------------------ *)
(* pure                                                                                             *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma hc4b_ke_add_saddrs_supd {A} (D: list (val * share * A)) a v : saddrs (supd D a v) = saddrs D.
Proof.
  induction D as [|[[x sh] w] D IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma hc4b_ke_add_saddrs_insert T a idx : saddrs (t_D (t_insert T a idx)) = saddrs (t_D T).
Proof.
  unfold t_insert, t_set_index. destruct (t_entry T a); simpl; auto.
  unfold t_upd; simpl. apply hc4b_ke_add_saddrs_supd.
Qed.

Lemma hc4b_ke_add_saddrs_kT T d KD :
  saddrs (t_D (kents_T T (d :: KD))) = kd_addr d :: saddrs (t_D (kents_T T KD)).
Proof.
  simpl kents_T. rewrite hc4b_ke_add_saddrs_insert. reflexivity.
Qed.

Lemma hc4b_ke_add_kT_incl T KD :
  incl (saddrs (t_D T)) (saddrs (t_D (kents_T T KD))) /\ incl (map kd_addr KD) (saddrs (t_D (kents_T T KD))).
Proof.
  induction KD as [|d KD [IH1 IH2]].
  - split; [apply incl_refl | intros x []].
  - rewrite hc4b_ke_add_saddrs_kT. split.
    + intros x Hx. right. auto.
    + intros x [<-|Hx]; [left; auto | right; auto].
Qed.

Lemma hc4b_ke_add_fill_addrs PS d : map peer_addr4 (fill_peers PS d) = map peer_addr4 PS.
Proof.
  unfold fill_peers. rewrite map_map. apply map_ext. intros [[a sh] P].
  destruct (eq_dec a (kd_owner d)); reflexivity.
Qed.

Lemma hc4b_ke_add_fill_wf PS d : peers_wf PS -> peers_wf (fill_peers PS d).
Proof.
  unfold peers_wf, fill_peers. intros H. apply Forall_map. eapply Forall_impl; [|exact H].
  intros [[a sh] P]. simpl. intros Hw. match goal with |- context [if ?c then _ else _] => destruct c end; auto.
Qed.

Lemma hc4b_ke_add_PS_addrs fl PS KD : map peer_addr4 (kents_PS fl PS KD) = map peer_addr4 PS.
Proof.
  induction KD as [|d KD IH]; simpl; auto.
  destruct fl; auto. rewrite hc4b_ke_add_fill_addrs. auto.
Qed.

Lemma hc4b_ke_add_PS_wf fl PS KD : peers_wf PS -> peers_wf (kents_PS fl PS KD).
Proof.
  intros H. induction KD as [|d KD IH]; simpl; auto.
  destruct fl; auto. apply hc4b_ke_add_fill_wf; auto.
Qed.

Lemma hc4b_ke_add_slots_mono own own' PS :
  incl own own' -> hc4b_ke_add_slots_ok own PS -> hc4b_ke_add_slots_ok own' PS.
Proof.
  intros I H. unfold hc4b_ke_add_slots_ok in *. eapply Forall_impl; [|exact H].
  intros [[a sh] P] HP. eapply Forall_impl; [|exact HP].
  intros x [Hx|Hx]; [left; auto | right; auto].
Qed.

Lemma hc4b_ke_add_slots_fill own PS d :
  In (kd_addr d) own -> hc4b_ke_add_slots_ok own PS -> hc4b_ke_add_slots_ok own (fill_peers PS d).
Proof.
  intros Hk H. unfold hc4b_ke_add_slots_ok, fill_peers in *. apply Forall_map.
  eapply Forall_impl; [|exact H]. intros [[a sh] P] HP. simpl.
  match goal with |- context [if ?c then _ else _] => destruct c end; auto.
  assert (Hk': vp_ok own (kd_addr d)) by (right; auto).
  inversion HP as [|? ? H1 HP1]; subst. inversion HP1 as [|? ? H2 HP2]; subst.
  inversion HP2 as [|? ? H3 _]; subst.
  unfold fill_slot.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    simpl; repeat first [apply Forall_nil | apply Forall_cons; [assumption|]].
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* separation                                                                                       *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma hc4b_ke_add_iter_in {B} (f: B -> mpred) (l: list B) x :
  In x l -> exists l1 l2, l = l1 ++ x :: l2 /\ iter_sepcon f l = f x * iter_sepcon f (l1 ++ l2).
Proof.
  intros H. destruct (in_split _ _ H) as (l1 & l2 & ->). exists l1, l2. split; auto.
  rewrite !iter_sepcon_app. simpl. apply pred_ext; cancel.
Qed.

Lemma hc4b_ke_add_in_addr (PS: list (val * share * peer)) a :
  In a (map peer_addr4 PS) -> exists sh P, In (a, sh, P) PS.
Proof.
  intros H. apply in_map_iff in H. destruct H as [[[x sh] P] [E H]]. simpl in E. subst. eauto.
Qed.

Lemma hc4b_ke_add_peer_ptr sh a P : peer_rep sh a P |-- !! isptr a.
Proof.
  unfold peer_rep. Intros. apply prop_right. destruct H; auto.
Qed.

Lemma hc4b_ke_add_peer_valid sh a P : readable_share sh -> peer_rep sh a P |-- valid_pointer a.
Proof.
  intros Hsh. unfold peer_rep. Intros.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0.
  - apply readable_nonidentity; auto.
  - simpl; lia.
  - reflexivity.
Qed.

Lemma hc4b_ke_add_peers_valid PS a Q :
  peers_wf PS -> In a (map peer_addr4 PS) -> Q * peers_rep PS |-- valid_pointer a.
Proof.
  intros W H. apply hc4b_ke_add_in_addr in H. destruct H as (sh & P & H).
  destruct (hc4b_ke_add_iter_in peer_item_rep PS _ H) as (l1 & l2 & E & E2).
  unfold peers_rep; rewrite E2.
  unfold peers_wf in W. rewrite Forall_forall in W. specialize (W _ H). simpl in W.
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1. simpl.
  apply hc4b_ke_add_peer_valid. auto.
Qed.

Lemma hc4b_ke_add_peers_ptr PS a :
  In a (map peer_addr4 PS) -> peers_rep PS |-- !! isptr a.
Proof.
  intros H. apply hc4b_ke_add_in_addr in H. destruct H as (sh & P & H).
  destruct (hc4b_ke_add_iter_in peer_item_rep PS _ H) as (l1 & l2 & E & E2).
  unfold peers_rep; rewrite E2.
  simpl. sep_apply hc4b_ke_add_peer_ptr. entailer!.
Qed.

Section NCS.
#[local] Existing Instance Noise.CS.
Lemma hc4b_ke_add_peer_conflict sh1 sh2 a P1 P2 :
  writable_share sh1 -> writable_share sh2 -> peer_rep sh1 a P1 * peer_rep sh2 a P2 |-- FF.
Proof.
  intros W1 W2. unfold peer_rep. Intros.
  rewrite !(@field_at_data_at Noise.CS _ t_peer (DOT I._device)).
  sep_apply (data_at_conflict_glb sh1 sh2 (tptr (Tstruct I._wg_device noattr)) (p_device P1) (p_device P2)
    (field_address t_peer (DOT I._device) a) (nonempty_writable_glb _ _ W1 (writable_readable_share W2))).
  rewrite FF_sepcon. apply derives_refl.
Qed.

Lemma hc4b_ke_add_peers_nodup PS : peers_wf PS -> peers_rep PS |-- !! NoDup (map peer_addr4 PS).
Proof.
  induction PS as [|[[a sh] P] PS IH]; intros W.
  - apply prop_right. constructor.
  - unfold peers_wf in W. inversion W as [|? ? Wa W']; subst.
    unfold peers_rep. simpl iter_sepcon. fold (peers_rep PS).
    assert_PROP (NoDup (map peer_addr4 PS)) as ND by (sep_apply (IH W'); entailer!).
    destruct (in_dec EqDec_val a (map peer_addr4 PS)) as [Hin|Hn].
    + apply hc4b_ke_add_in_addr in Hin. destruct Hin as (sh2 & P2 & Hin).
      destruct (hc4b_ke_add_iter_in peer_item_rep PS _ Hin) as (l1 & l2 & E & E2).
      unfold peers_rep. rewrite E2. simpl.
      rewrite Forall_forall in W'. specialize (W' _ Hin). simpl in W'.
      sep_apply (hc4b_ke_add_peer_conflict sh sh2 a P P2); auto. normalize.
    + apply prop_right. simpl. constructor; auto.
Qed.

(* a raw entry at k and the index table: k is not in the pool *)
Lemma hc4b_ke_add_notin sht tab T v k :
  @data_at Noise.CS Ews t_entry_s v k * itable sht tab T |-- !! ~ In k (saddrs (t_D T)).
Proof.
  destruct (in_dec EqDec_val k (saddrs (t_D T))) as [Hin|Hn]; [|apply prop_right; auto].
  destruct (hc4b_ke_hf2_sfind_in _ _ Hin) as (sh & E & F).
  unfold itable. Intros. rewrite (hc4b_ke_hf2_split_at _ _ _ _ _ F).
  assert (Wsh: writable_share sh).
  { destruct H as (_ & _ & _ & HF). apply hc4b_ke_hf2_sfind_In in F.
    rewrite Forall_forall in HF. apply (HF _ F). }
  unfold pool_item_rep, entry_at.
  sep_apply (data_at_conflict_glb Ews sh t_entry_s v (entry_val E (succ_in (t_L T) k) (vin k (t_L T))) k
    (nonempty_writable_glb _ _ writable_Ews (writable_readable_share Wsh))).
  rewrite FF_sepcon. apply FF_left.
Qed.
End NCS.

Lemma hc4b_ke_add_wand_frame (F D X: mpred) : (F -* D) * X |-- F -* (D * X).
Proof.
  apply (proj1 (wand_sepcon_adjoint _ _ _)).
  rewrite sepcon_assoc, (sepcon_comm X F), <- sepcon_assoc.
  apply sepcon_derives; [|apply derives_refl]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Section Hn.
Variable CSw: compspecs.
#[local] Existing Instance CS4.

#[local] Instance hc4b_ke_add_cce1 : change_composite_env CKS CS4.
Proof. make_cs_preserve CKS CS4. Defined.

Lemma hc4b_ke_add_p_cs v l :
  @field_at CKS Ews t_hnode4 (DOT HC._p) v l = @field_at CS4 Ews t_hnode4 (DOT HC._p) v l.
Proof.
  exact (f_equal (fun f => f l)
    (@field_at_change_composite CKS CS4 _ Ews t_hnode4 (DOT HC._p) v v (JMeq_refl v) eq_refl)).
Qed.

Lemma hc4b_ke_add_node_p (pp: val) sn r rs nx l :
  @data_at CKS Ews t_hnode4 (pp, (sn, (r, (rs, nx)))) l |--
  @field_at CS4 Ews t_hnode4 (DOT HC._p) pp l * (@field_at CS4 Ews t_hnode4 (DOT HC._p) pp l -*
    @data_at CKS Ews t_hnode4 (pp, (sn, (r, (rs, nx)))) l).
Proof.
  assert_PROP (@field_compatible CKS t_hnode4 [] l) as FC by entailer!.
  unfold data_at.
  assert (FC1: @field_compatible CKS t_hnode4 (DOT HC._p) l) by auto with field_compatible.
  sep_apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) (pp, (sn, (r, (rs, nx)))) pp l (JMeq_refl pp) FC1).
  rewrite <- !hc4b_ke_add_p_cs.
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ pp). apply derives_refl.
Qed.

Lemma hc4b_ke_add_hn_valid l NS : hnodes_rep4 CSw l NS |-- valid_pointer l.
Proof.
  destruct NS as [|N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4b_ke_add_hn_p l NS j : 0 <= j < Zlength NS ->
  hnodes_rep4 CSw l NS |--
  @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p (Znth j NS)) (hn_addr (Znth j NS)) *
  (@field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p (Znth j NS)) (hn_addr (Znth j NS)) -* hnodes_rep4 CSw l NS).
Proof.
  revert l j. induction NS as [|N NS IH]; intros l j Hj.
  - rewrite Zlength_nil in Hj. lia.
  - rewrite Zlength_cons in Hj. simpl hnodes_rep4. Intros nx. subst l.
    destruct (zeq j 0) as [->|Hj0].
    + rewrite Znth_0_cons.
      sep_apply hc4b_ke_add_node_p. cancel.
      set (F := @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N)).
      set (D := @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
      set (X := @malloc_token CSw Ews t_hnode4 (hn_addr N) * @malloc_token CSw Ews t_peer (hn_p N) *
                hnodes_rep4 CSw nx NS).
      apply derives_trans with ((F -* D) * X); [unfold X, D; cancel|].
      eapply derives_trans; [apply hc4b_ke_add_wand_frame|].
      apply wand_derives; [apply derives_refl|]. unfold D, X. Exists nx. entailer!.
    + rewrite Znth_pos_cons by lia.
      sep_apply (IH nx (j - 1) ltac:(lia)). cancel.
      set (F := @field_at CS4 Ews t_hnode4 (DOT HC._p) (hn_p (Znth (j - 1) NS)) (hn_addr (Znth (j - 1) NS))).
      set (X := @malloc_token CSw Ews t_hnode4 (hn_addr N) *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) *
        @malloc_token CSw Ews t_peer (hn_p N)).
      apply derives_trans with ((F -* hnodes_rep4 CSw nx NS) * X); [unfold X; cancel|].
      eapply derives_trans; [apply hc4b_ke_add_wand_frame|].
      apply wand_derives; [apply derives_refl|]. unfold X. Exists nx. entailer!.
Qed.
End Hn.
