(*
   - accessors (P |-- Q * (Q -* P)) for the node (ONE value at the world W: hcl5_p7_nv), its p, refs, snapshot
     (HCS, for hs_same_but_next) and rest (CKS, for pr_same) fields, the peer's reference count (at W);
   - pure facts: the snapshot in T vs in T without another entry (snap_eqb_nn = true), pr_eqb reflexive, the
     peers after the clear of another peer, the lent objects' addresses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_defs.
Local Open Scope logic.

#[export] Instance hcl5_p7_chk_cceN : change_composite_env Noise.CS W_handshake_clear.
Proof. make_cs_preserve Noise.CS W_handshake_clear. Defined.
#[export] Instance hcl5_p7_chk_cceH : change_composite_env HCS W_handshake_clear.
Proof. make_cs_preserve HCS W_handshake_clear. Defined.
#[export] Instance hcl5_p7_chk_cceK : change_composite_env CKS W_handshake_clear.
Proof. make_cs_preserve CKS W_handshake_clear. Defined.

(* ---------------------------------------------------------------------- *)
(* accessors                                                               *)
(* ---------------------------------------------------------------------- *)

Definition hcl5_p7_chk_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hcl5_p7_chk_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hcl5_p7_chk_acc_refl Q : hcl5_p7_chk_acc Q Q.
Proof.
  unfold hcl5_p7_chk_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hcl5_p7_chk_acc_eq Q A : Q = A -> hcl5_p7_chk_acc Q A.
Proof. intros ->. apply hcl5_p7_chk_acc_refl. Qed.

Lemma hcl5_p7_chk_acc_l Q A F : hcl5_p7_chk_acc Q A -> hcl5_p7_chk_acc Q (A * F).
Proof.
  unfold hcl5_p7_chk_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hcl5_p7_chk_acc_r Q A F : hcl5_p7_chk_acc Q A -> hcl5_p7_chk_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hcl5_p7_chk_acc_l, H. Qed.

Lemma hcl5_p7_chk_acc_prop Q (c: Prop) A : (c -> hcl5_p7_chk_acc Q A) -> hcl5_p7_chk_acc Q (!! c && A).
Proof.
  unfold hcl5_p7_chk_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcl5_p7_chk_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hcl5_p7_chk_acc Q (A x)) -> hcl5_p7_chk_acc Q (EX x, A x).
Proof.
  unfold hcl5_p7_chk_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

Lemma hcl5_p7_chk_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hcl5_p7_chk_acc Q A) -> hcl5_p7_chk_acc Q A.
Proof.
  unfold hcl5_p7_chk_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hcl5_p7_chk_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hcl5_p7_chk_acc Q (f x) -> hcl5_p7_chk_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hcl5_p7_chk_acc_l, H | apply hcl5_p7_chk_acc_r, IH, Hin].
Qed.

Lemma hcl5_p7_chk_acc_trans Q B P : hcl5_p7_chk_acc Q B -> hcl5_p7_chk_acc B P -> hcl5_p7_chk_acc Q P.
Proof.
  unfold hcl5_p7_chk_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

(* ---------------------------------------------------------------------- *)
(* the target node                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p7_chk_split {A: Type} {d: Inhabitant A} (l: list A) i : 0 <= i < Zlength l ->
  l = sublist 0 i l ++ Znth i l :: sublist (i + 1) (Zlength l) l.
Proof.
  intros Hi. rewrite <- (sublist_same 0 (Zlength l) l) at 1 by auto.
  rewrite (sublist_split 0 i (Zlength l)) by lia. rewrite (sublist_split i (i + 1) (Zlength l)) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma hcl5_p7_chk_len_peers NS PS : hnodes_peers4 NS PS -> Zlength NS = Zlength PS.
Proof.
  unfold hnodes_peers4. intros E. rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS), E.
  reflexivity.
Qed.

Lemma hcl5_p7_chk_hn_p NS PS i : hnodes_peers4 NS PS -> 0 <= i < Zlength NS ->
  hn_p (Znth i NS) = peer_addr4 (Znth i PS).
Proof.
  intros E Hi. pose proof (hcl5_p7_chk_len_peers _ _ E) as HL.
  rewrite <- (Znth_map i hn_p NS) by lia. rewrite <- (Znth_map i peer_addr4 PS) by lia.
  unfold hnodes_peers4 in E. rewrite E. reflexivity.
Qed.

(* the snapshot field of a node (HCS), the rest field (CKS) *)
Lemma hcl5_p7_chk_HW sh (v: @reptype HCS t_hsnap) y :
  @data_at HCS sh t_hsnap v y = @data_at W_handshake_clear sh t_hsnap v y.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hcl5_p7_chk_PW sh (v: @reptype CKS t_prsnap) y :
  @data_at CKS sh t_prsnap v y = @data_at W_handshake_clear sh t_prsnap v y.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Section Wsec.
#[local] Existing Instance W_handshake_clear.

Lemma hcl5_p7_chk_node_snap sh p sn P nx x :
  data_at sh t_hnode4 (hcl5_p7_nv p sn P nx) x |--
  @data_at HCS sh t_hsnap (hsnap_val sn) (field_address t_hnode4 [StructField HC._snap] x) *
  (@data_at HCS sh t_hsnap (hsnap_val sn) (field_address t_hnode4 [StructField HC._snap] x) -*
   data_at sh t_hnode4 (hcl5_p7_nv p sn P nx) x).
Proof.
  unfold hcl5_p7_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._snap) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives.
  - rewrite field_at_data_at. rewrite hcl5_p7_chk_HW. apply derives_refl.
  - apply (allp_left _ (hsnap_val sn)). apply wand_derives.
    + rewrite field_at_data_at. rewrite hcl5_p7_chk_HW. apply derives_refl.
    + apply derives_refl.
Qed.

Lemma hcl5_p7_chk_node_rest sh p sn P nx x :
  data_at sh t_hnode4 (hcl5_p7_nv p sn P nx) x |--
  @data_at CKS sh t_prsnap (prsnap_val P) (field_address t_hnode4 [StructField HC._rest] x) *
  (@data_at CKS sh t_prsnap (prsnap_val P) (field_address t_hnode4 [StructField HC._rest] x) -*
   data_at sh t_hnode4 (hcl5_p7_nv p sn P nx) x).
Proof.
  unfold hcl5_p7_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._rest) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives.
  - rewrite field_at_data_at. rewrite hcl5_p7_chk_PW. apply derives_refl.
  - apply (allp_left _ (prsnap_val P)). apply wand_derives.
    + rewrite field_at_data_at. rewrite hcl5_p7_chk_PW. apply derives_refl.
    + apply derives_refl.
Qed.

Lemma hcl5_p7_chk_node_p sh p sn P nx x :
  data_at sh t_hnode4 (hcl5_p7_nv p sn P nx) x |--
  field_at sh t_hnode4 [StructField HC._p] p x *
  (field_at sh t_hnode4 [StructField HC._p] p x -* data_at sh t_hnode4 (hcl5_p7_nv p sn P nx) x).
Proof.
  unfold hcl5_p7_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._p) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p). apply derives_refl.
Qed.

Lemma hcl5_p7_chk_node_refs sh p sn P nx x :
  data_at sh t_hnode4 (hcl5_p7_nv p sn P nx) x |--
  field_at sh t_hnode4 [StructField HC._refs] (Vint (p_refs P)) x *
  (field_at sh t_hnode4 [StructField HC._refs] (Vint (p_refs P)) x -* data_at sh t_hnode4 (hcl5_p7_nv p sn P nx) x).
Proof.
  unfold hcl5_p7_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._refs) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ (Vint (p_refs P))). apply derives_refl.
Qed.

End Wsec.

(* pure facts on the table *)
Lemma hcl5_p7_chk_sfind_in (D: list (val * share * entry)) a : In a (saddrs D) ->
  exists sh E, sfind D a = Some (sh, E) /\ In (a, sh, E) D.
Proof.
  induction D as [|[[x sh] v] D IH]; intros H; [destruct H|].
  cbn [saddrs map sfind] in *. destruct (eq_dec x a) as [->|n].
  - exists sh, v; split; [reflexivity | left; reflexivity].
  - destruct H as [H|H]; [congruence|]. destruct (IH H) as (sh' & E & H1 & H2).
    exists sh', E; split; [exact H1 | right; exact H2].
Qed.

Lemma hcl5_p7_chk_vremove_notin a l : ~ In a (vremove a l).
Proof.
  induction l as [|x l IH]; simpl; [auto|]. destruct (EqDec_val x a) as [->|n]; [exact IH|].
  intros [H|H]; [congruence | exact (IH H)].
Qed.

Lemma hcl5_p7_chk_succ_notin a l : ~ In a l -> succ_in l a = nullval.
Proof.
  induction l as [|x l IH]; simpl; [auto|]. intros H. destruct (EqDec_val x a) as [->|n].
  - exfalso; apply H; left; reflexivity.
  - apply IH. intros H'; apply H; right; exact H'.
Qed.

Lemma hcl5_p7_chk_vin_false a l : ~ In a l -> vin a l = false.
Proof. intros H. unfold vin. destruct (in_dec eq_dec a l); [contradiction | reflexivity]. Qed.

Lemma hcl5_p7_chk_vin_true a l : vin a l = false -> ~ In a l.
Proof. unfold vin. destruct (in_dec eq_dec a l); [discriminate | auto]. Qed.

(* ---------------------------------------------------------------------- *)
(* the peer: its reference count at W                                      *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p7_chk_peer_refs sh p P :
  hcl5_p7_chk_acc (@field_at W_handshake_clear sh t_peer [StructField HCL5._refcount] (Vint (p_refs P)) p)
    (peer_rep sh p P).
Proof.
  unfold peer_rep. apply hcl5_p7_chk_acc_prop; intros _.
  do 4 apply hcl5_p7_chk_acc_l. apply hcl5_p7_chk_acc_r. apply hcl5_p7_chk_acc_eq.
  rewrite (@field_at_change_composite Noise.CS W_handshake_clear _ sh t_peer [StructField I._refcount]
    (Vint (p_refs P)) (Vint (p_refs P)) (JMeq_refl _)) by prove_cs_preserve_type.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p7_chk_veqb x : veqb x x = true.
Proof. unfold veqb. rewrite if_true; reflexivity. Qed.

Lemma hcl5_p7_chk_bytes_eqb l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. rewrite if_true; reflexivity. Qed.

Lemma hcl5_p7_chk_pr_eqb P H : pr_eqb P (p_set_hs P H) = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb, p_set_hs. cbn [p_device p_dead p_cur p_prev p_next p_lsh p_id p_pknext p_cookie].
  rewrite !hcl5_p7_chk_veqb, !Int64.eq_true, !hcl5_p7_chk_bytes_eqb, !eqb_reflx. reflexivity.
Qed.

Lemma hcl5_p7_chk_peers_split i PS x : 0 <= i < Zlength PS ->
  peers_rep (upd_Znth i PS x) =
  peer_item_rep x * peers_rep (sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS).
Proof.
  intros Hi. rewrite upd_Znth_unfold by auto. unfold peers_rep. rewrite !iter_sepcon_app. simpl.
  apply pred_ext; cancel.
Qed.

Lemma hcl5_p7_chk_pknext_l l1 a sh P l2 head : pk_chain head (l1 ++ (a, sh, P) :: l2) ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 l2).
Proof.
  revert head; induction l1 as [|[[b shb] Q] l1 IH]; intros head H; simpl in H.
  - destruct H as [_ H]. destruct l2 as [|[[c shc] R] l2]; simpl in H.
    + left; exact H.
    + right. destruct H as [-> _]. left; reflexivity.
  - destruct H as [_ H]. exact (IH _ H).
Qed.

Lemma hcl5_p7_chk_pknext head PS i p sh P : pk_chain head PS -> 0 <= i < Zlength PS -> Znth i PS = (p, sh, P) ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 (sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS)).
Proof.
  intros H Hi E. rewrite (hcl5_p7_chk_split PS i Hi), E in H.
  destruct (hcl5_p7_chk_pknext_l _ _ _ _ _ _ H) as [H1|H1]; [left; exact H1|].
  right. rewrite map_app, in_app_iff. right; exact H1.
Qed.

(* ---------------------------------------------------------------------- *)
(* the node k <> i: its peer, the other peers, the table                   *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p7_chk_peers_at k PS : 0 <= k < Zlength PS ->
  peers_rep PS = peer_item_rep (Znth k PS) * peers_rep (sublist 0 k PS ++ sublist (k + 1) (Zlength PS) PS).
Proof.
  intros Hk. rewrite (hcl5_p7_chk_split PS k Hk) at 1. unfold peers_rep. rewrite !iter_sepcon_app. simpl.
  apply pred_ext; cancel.
Qed.

Lemma hcl5_p7_chk_clr_len i PS : 0 <= i < Zlength PS -> Zlength (hcl5_clr i PS) = Zlength PS.
Proof. intros Hi. unfold hcl5_clr. apply upd_Znth_Zlength; auto. Qed.

Lemma hcl5_p7_chk_clr_nth i k PS : 0 <= i < Zlength PS -> 0 <= k < Zlength PS -> k <> i ->
  Znth k (hcl5_clr i PS) = Znth k PS.
Proof. intros Hi Hk Hn. unfold hcl5_clr. apply upd_Znth_diff; auto. Qed.

Lemma hcl5_p7_chk_clr_map {B: Type} {dB: Inhabitant B} (f: val * share * peer -> B) i PS : 0 <= i < Zlength PS ->
  (forall x, f (hcl5_clr1 x) = f x) -> map f (hcl5_clr i PS) = map f PS.
Proof.
  intros Hi Hf. pose proof (hcl5_p7_chk_clr_len i PS Hi) as HL.
  apply Znth_eq_ext; [rewrite !Zlength_map; exact HL|].
  intros j Hj. rewrite Zlength_map, HL in Hj. rewrite !Znth_map by lia.
  unfold hcl5_clr. destruct (Z.eq_dec j i) as [->|n].
  - rewrite upd_Znth_same by lia. apply Hf.
  - rewrite upd_Znth_diff by lia. reflexivity.
Qed.

Lemma hcl5_p7_chk_others_addrs i k PS : 0 <= i < Zlength PS ->
  map peer_addr4 (sublist 0 k (hcl5_clr i PS) ++ sublist (k + 1) (Zlength (hcl5_clr i PS)) (hcl5_clr i PS)) =
  map peer_addr4 (sublist 0 k PS ++ sublist (k + 1) (Zlength PS) PS).
Proof.
  intros Hi. rewrite hcl5_p7_chk_clr_len by auto. rewrite !map_app, <- !sublist_map.
  rewrite (hcl5_p7_chk_clr_map peer_addr4) by (auto; intros [[a sh] P]; reflexivity). reflexivity.
Qed.

Definition hcl5_p7_chk_shok (x: val * share * peer) : Prop := match x with (_, sh, _) => sh = Ews end.

Lemma hcl5_p7_chk_others_sh i k PS : 0 <= i < Zlength PS -> Forall hcl5_p7_chk_shok PS ->
  Forall (fun y => match y with (_, sh, _) => sh = Ews end)
    (sublist 0 k (hcl5_clr i PS) ++ sublist (k + 1) (Zlength (hcl5_clr i PS)) (hcl5_clr i PS)).
Proof.
  intros Hi HF.
  set (g := fun x: val * share * peer => match x with (_, sh, _) => sh end).
  assert (E: map g (hcl5_clr i PS) = map g PS) by (apply (@hcl5_p7_chk_clr_map share Tsh); auto; intros [[a sh] P]; reflexivity).
  assert (HC: Forall hcl5_p7_chk_shok (hcl5_clr i PS)).
  { rewrite Forall_forall in HF |- *. intros x Hx.
    assert (Hg: In (g x) (map g PS)) by (rewrite <- E; apply in_map, Hx).
    apply in_map_iff in Hg. destruct Hg as (y & Ey & Hy). specialize (HF y Hy).
    destruct x as [[a sh] P], y as [[b sh'] P']. unfold hcl5_p7_chk_shok, g in *. congruence. }
  apply Forall_app; split; apply Forall_sublist; exact HC.
Qed.

Lemma hcl5_p7_chk_ne (D: list (val * share * entry)) KE PS i k :
  saddrs D = map ke_addr KE ++ map (fun x => hs_addr (peer_addr4 x)) PS -> NoDup (saddrs D) ->
  0 <= i < Zlength PS -> 0 <= k < Zlength PS -> k <> i ->
  hs_addr (peer_addr4 (Znth k PS)) <> hs_addr (peer_addr4 (Znth i PS)).
Proof.
  intros Hs Hnd Hi Hk Hn E. rewrite Hs in Hnd. apply NoDup_app_remove_l in Hnd.
  apply Hn. apply (NoDup_Znth_inj _ k i Hnd); rewrite ?Zlength_map; auto.
  rewrite !Znth_map by lia. exact E.
Qed.

Lemma hcl5_p7_chk_vremove_in a b l : b <> a -> (In b (vremove a l) <-> In b l).
Proof.
  intros H. induction l as [|x l IH]; simpl; [tauto|].
  destruct (EqDec_val x a) as [->|n]; simpl; rewrite IH; [|tauto].
  split; [auto|]. intros [E|E]; [congruence | exact E].
Qed.

Lemma hcl5_p7_chk_vin_remove a b l : b <> a -> vin b (vremove a l) = vin b l.
Proof.
  intros H. unfold vin. pose proof (hcl5_p7_chk_vremove_in a b l H) as E.
  destruct (in_dec eq_dec b (vremove a l)), (in_dec eq_dec b l); tauto.
Qed.

Lemma hcl5_p7_chk_entry_refl E : entry_eqb E E = true.
Proof. unfold entry_eqb. rewrite if_true by reflexivity. rewrite !Int.eq_true. reflexivity. Qed.

Lemma hcl5_p7_chk_hs_refl H : hs_eqb H H = true.
Proof.
  unfold hs_eqb. rewrite !Int.eq_true, Int64.eq_true, !hcl5_p7_chk_bytes_eqb. rewrite if_true by reflexivity.
  reflexivity.
Qed.

Lemma hcl5_p7_chk_snap T a q Q : hs_addr q <> a ->
  snap_eqb_nn (hs_snap_cur T q Q) (hs_snap_cur (t_remove T a) q Q) = true.
Proof.
  intros H. unfold hs_snap_cur, snap_of, snap_eqb_nn. cbn [sn_entry sn_hashed sn_hs].
  change (t_entry_d (t_remove T a) (hs_addr q)) with (t_entry_d T (hs_addr q)).
  cbn [t_remove t_L]. rewrite hcl5_p7_chk_vin_remove by auto.
  rewrite eqb_reflx, hcl5_p7_chk_entry_refl, hcl5_p7_chk_hs_refl. reflexivity.
Qed.

Lemma hcl5_p7_chk_pr_refl P : pr_eqb P P = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb.
  rewrite !hcl5_p7_chk_veqb, !Int64.eq_true, !hcl5_p7_chk_bytes_eqb, !eqb_reflx. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the lent objects                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p7_chk_peer_fc sh p P : peer_rep sh p P |-- !! @field_compatible Noise.CS t_peer [] p.
Proof. unfold peer_rep. entailer!. Qed.

Lemma hcl5_p7_chk_vo1 sh wg D : vobjs W_handshake_clear [VDev sh wg D] = device_rep sh wg D.
Proof. unfold vobjs. simpl. apply sepcon_emp. Qed.

(* the objects lent to pr_same: the device, the index table (v4.1: the kents' addresses = the keypair slots are
   pool entries of the table), the other peers (pubkey_next) *)
Definition hcl5_p7_chk_VO (wg: val) (D: device) (it: val) (T': tstate) (others: list (val * share * peer))
  : list vobj :=
  [VDev Tsh wg D; VItab Tsh it T'; VPeers others].

Lemma hcl5_p7_chk_vo3 wg D it T' others :
  vobjs W_handshake_clear (hcl5_p7_chk_VO wg D it T' others) =
  (device_rep Tsh wg D * itable Tsh it T' * peers_rep others)%logic.
Proof. unfold vobjs, hcl5_p7_chk_VO. simpl. rewrite sepcon_emp, sepcon_assoc. reflexivity. Qed.

Lemma hcl5_p7_chk_kaddrs T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. reflexivity. Qed.

Lemma hcl5_p7_chk_vp p wg D it T' others P :
  p_device P = wg ->
  Forall (fun k => k = nullval \/ In k (saddrs (t_D T'))) [p_cur P; p_prev P; p_next P] ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 others) ->
  Forall (vp_ok (p :: vobjs_addrs (hcl5_p7_chk_VO wg D it T' others))) (pr_ptrs P P).
Proof.
  intros Hd Hs Hpk.
  assert (E: vobjs_addrs (hcl5_p7_chk_VO wg D it T' others) =
             [wg; id_addr wg; cc_addr wg] ++ (it :: saddrs (t_D T')) ++ map peer_addr4 others).
  { unfold vobjs_addrs, hcl5_p7_chk_VO. simpl. rewrite app_nil_r. reflexivity. }
  rewrite E. clear E.
  set (A := p :: [wg; id_addr wg; cc_addr wg] ++ (it :: saddrs (t_D T')) ++ map peer_addr4 others).
  assert (Hk: forall k, k = nullval \/ In k (saddrs (t_D T')) -> vp_ok A k).
  { intros k [Hk|Hk]; [left; exact Hk |]. right. subst A. right. rewrite in_app_iff. right.
    rewrite in_app_iff. left. right. exact Hk. }
  assert (Hdv: vp_ok A (p_device P)).
  { right. subst A. right. rewrite Hd. left. reflexivity. }
  assert (Hpv: vp_ok A (p_pknext P)).
  { destruct Hpk as [Hpk|Hpk]; [left; exact Hpk|].
    right. subst A. right. rewrite in_app_iff; right; rewrite in_app_iff; right; exact Hpk. }
  inversion Hs as [|a l Hc Hs1]; subst. inversion Hs1 as [|b l' Hp Hs2]; subst.
  inversion Hs2 as [|c l'' Hn _]; subst.
  unfold pr_ptrs.
  repeat apply Forall_cons; try apply Forall_nil; auto.
Qed.
