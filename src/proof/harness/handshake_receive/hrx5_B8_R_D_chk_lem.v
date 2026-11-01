(*
   - accessors (P |-- Q * (Q -* P)) for the node (ONE value at the world W: hrx5_B8RD_nv), its p, refs, snapshot
     (HCS, for hs_same_but_next) and rest (CKS, for pr_same) fields, the peer's reference count (at W);
   - pure facts: the snapshot in T vs in Tf (snap_eqb_nn = true), pr_eqb reflexive, the peers
     upd_Znth j PS (a, Ews, Pf) seen from k <> j, the pool (hrx5cr_pool), the lent objects' addresses. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_defs.
Local Open Scope logic.

#[export] Instance hrx5_B8RDc_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.
#[export] Instance hrx5_B8RDc_cceH : change_composite_env HCS W_handshake_receive.
Proof. make_cs_preserve HCS W_handshake_receive. Defined.
#[export] Instance hrx5_B8RDc_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.

(* ---------------------------------------------------------------------- *)
(* accessors                                                               *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8RDc_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B8RDc_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hrx5_B8RDc_acc_refl Q : hrx5_B8RDc_acc Q Q.
Proof.
  unfold hrx5_B8RDc_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B8RDc_acc_eq Q A : Q = A -> hrx5_B8RDc_acc Q A.
Proof. intros ->. apply hrx5_B8RDc_acc_refl. Qed.

Lemma hrx5_B8RDc_acc_l Q A F : hrx5_B8RDc_acc Q A -> hrx5_B8RDc_acc Q (A * F).
Proof.
  unfold hrx5_B8RDc_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B8RDc_acc_r Q A F : hrx5_B8RDc_acc Q A -> hrx5_B8RDc_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B8RDc_acc_l, H. Qed.

Lemma hrx5_B8RDc_acc_prop Q (c: Prop) A : (c -> hrx5_B8RDc_acc Q A) -> hrx5_B8RDc_acc Q (!! c && A).
Proof.
  unfold hrx5_B8RDc_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8RDc_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_B8RDc_acc Q (A x)) -> hrx5_B8RDc_acc Q (EX x, A x).
Proof.
  unfold hrx5_B8RDc_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

Lemma hrx5_B8RDc_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hrx5_B8RDc_acc Q A) -> hrx5_B8RDc_acc Q A.
Proof.
  unfold hrx5_B8RDc_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hrx5_B8RDc_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hrx5_B8RDc_acc Q (f x) -> hrx5_B8RDc_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hrx5_B8RDc_acc_l, H | apply hrx5_B8RDc_acc_r, IH, Hin].
Qed.

Lemma hrx5_B8RDc_acc_trans Q B P : hrx5_B8RDc_acc Q B -> hrx5_B8RDc_acc B P -> hrx5_B8RDc_acc Q P.
Proof.
  unfold hrx5_B8RDc_acc. intros H1 H2. eapply derives_trans; [exact H2|].
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

Lemma hrx5_B8RDc_split {A: Type} {d: Inhabitant A} (l: list A) i : 0 <= i < Zlength l ->
  l = sublist 0 i l ++ Znth i l :: sublist (i + 1) (Zlength l) l.
Proof.
  intros Hi. rewrite <- (sublist_same 0 (Zlength l) l) at 1 by auto.
  rewrite (sublist_split 0 i (Zlength l)) by lia. rewrite (sublist_split i (i + 1) (Zlength l)) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma hrx5_B8RDc_len_peers NS PS : hnodes_peers4 NS PS -> Zlength NS = Zlength PS.
Proof.
  unfold hnodes_peers4. intros E. rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS), E.
  reflexivity.
Qed.

Lemma hrx5_B8RDc_hn_p NS PS i : hnodes_peers4 NS PS -> 0 <= i < Zlength NS ->
  hn_p (Znth i NS) = peer_addr4 (Znth i PS).
Proof.
  intros E Hi. pose proof (hrx5_B8RDc_len_peers _ _ E) as HL.
  rewrite <- (Znth_map i hn_p NS) by lia. rewrite <- (Znth_map i peer_addr4 PS) by lia.
  unfold hnodes_peers4 in E. rewrite E. reflexivity.
Qed.

(* the snapshot field of a node (HCS), the rest field (CKS) *)
Lemma hrx5_B8RDc_HW sh (v: @reptype HCS t_hsnap) y :
  @data_at HCS sh t_hsnap v y = @data_at W_handshake_receive sh t_hsnap v y.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hrx5_B8RDc_PW sh (v: @reptype CKS t_prsnap) y :
  @data_at CKS sh t_prsnap v y = @data_at W_handshake_receive sh t_prsnap v y.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Section Wsec.
#[local] Existing Instance W_handshake_receive.

Lemma hrx5_B8RDc_node_snap sh p sn P nx x :
  data_at sh t_hnode4 (hrx5_B8RD_nv p sn P nx) x |--
  @data_at HCS sh t_hsnap (hsnap_val sn) (field_address t_hnode4 [StructField HC._snap] x) *
  (@data_at HCS sh t_hsnap (hsnap_val sn) (field_address t_hnode4 [StructField HC._snap] x) -*
   data_at sh t_hnode4 (hrx5_B8RD_nv p sn P nx) x).
Proof.
  unfold hrx5_B8RD_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._snap) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives.
  - rewrite field_at_data_at. rewrite hrx5_B8RDc_HW. apply derives_refl.
  - apply (allp_left _ (hsnap_val sn)). apply wand_derives.
    + rewrite field_at_data_at. rewrite hrx5_B8RDc_HW. apply derives_refl.
    + apply derives_refl.
Qed.

Lemma hrx5_B8RDc_node_rest sh p sn P nx x :
  data_at sh t_hnode4 (hrx5_B8RD_nv p sn P nx) x |--
  @data_at CKS sh t_prsnap (prsnap_val P) (field_address t_hnode4 [StructField HC._rest] x) *
  (@data_at CKS sh t_prsnap (prsnap_val P) (field_address t_hnode4 [StructField HC._rest] x) -*
   data_at sh t_hnode4 (hrx5_B8RD_nv p sn P nx) x).
Proof.
  unfold hrx5_B8RD_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._rest) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives.
  - rewrite field_at_data_at. rewrite hrx5_B8RDc_PW. apply derives_refl.
  - apply (allp_left _ (prsnap_val P)). apply wand_derives.
    + rewrite field_at_data_at. rewrite hrx5_B8RDc_PW. apply derives_refl.
    + apply derives_refl.
Qed.

Lemma hrx5_B8RDc_node_p sh p sn P nx x :
  data_at sh t_hnode4 (hrx5_B8RD_nv p sn P nx) x |--
  field_at sh t_hnode4 [StructField HC._p] p x *
  (field_at sh t_hnode4 [StructField HC._p] p x -* data_at sh t_hnode4 (hrx5_B8RD_nv p sn P nx) x).
Proof.
  unfold hrx5_B8RD_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._p) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p). apply derives_refl.
Qed.

Lemma hrx5_B8RDc_node_refs sh p sn P nx x :
  data_at sh t_hnode4 (hrx5_B8RD_nv p sn P nx) x |--
  field_at sh t_hnode4 [StructField HC._refs] (Vint (p_refs P)) x *
  (field_at sh t_hnode4 [StructField HC._refs] (Vint (p_refs P)) x -* data_at sh t_hnode4 (hrx5_B8RD_nv p sn P nx) x).
Proof.
  unfold hrx5_B8RD_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._refs) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ (Vint (p_refs P))). apply derives_refl.
Qed.

End Wsec.

(* pure facts on the table *)
Lemma hrx5_B8RDc_sfind_in (D: list (val * share * entry)) a : In a (saddrs D) ->
  exists sh E, sfind D a = Some (sh, E) /\ In (a, sh, E) D.
Proof.
  induction D as [|[[x sh] v] D IH]; intros H; [destruct H|].
  cbn [saddrs map sfind] in *. destruct (eq_dec x a) as [->|n].
  - exists sh, v; split; [reflexivity | left; reflexivity].
  - destruct H as [H|H]; [congruence|]. destruct (IH H) as (sh' & E & H1 & H2).
    exists sh', E; split; [exact H1 | right; exact H2].
Qed.

Lemma hrx5_B8RDc_vremove_notin a l : ~ In a (vremove a l).
Proof.
  induction l as [|x l IH]; simpl; [auto|]. destruct (EqDec_val x a) as [->|n]; [exact IH|].
  intros [H|H]; [congruence | exact (IH H)].
Qed.

Lemma hrx5_B8RDc_succ_notin a l : ~ In a l -> succ_in l a = nullval.
Proof.
  induction l as [|x l IH]; simpl; [auto|]. intros H. destruct (EqDec_val x a) as [->|n].
  - exfalso; apply H; left; reflexivity.
  - apply IH. intros H'; apply H; right; exact H'.
Qed.

Lemma hrx5_B8RDc_vin_false a l : ~ In a l -> vin a l = false.
Proof. intros H. unfold vin. destruct (in_dec eq_dec a l); [contradiction | reflexivity]. Qed.

Lemma hrx5_B8RDc_vin_true a l : vin a l = false -> ~ In a l.
Proof. unfold vin. destruct (in_dec eq_dec a l); [discriminate | auto]. Qed.

(* ---------------------------------------------------------------------- *)
(* the peer: its reference count at W                                      *)
(* ---------------------------------------------------------------------- *)

Section Wsec2.
#[local] Existing Instance W_handshake_receive.

Lemma hrx5_B8RDc_kref sh p (v: val) :
  @field_at W_handshake_receive sh t_peer (DOT HC._refcount) v p =
  @field_at W_handshake_receive sh t_peer (DOT HC._refcount DOT HC._refcount) v p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hrx5_B8RDc_peer_refs sh p P :
  hrx5_B8RDc_acc (@field_at W_handshake_receive sh t_peer (DOT HC._refcount DOT HC._refcount) (Vint (p_refs P)) p)
    (peer_rep sh p P).
Proof.
  unfold hrx5_B8RDc_acc, peer_rep. Intros.
  match goal with |- ?a1 * ?a2 * ?a3 * ?a4 * ?a5 * ?a6 * ?F * ?a8 * ?a9 * ?a10 * ?a11 |-- _ =>
    apply derives_trans with (F * (a1 * a2 * a3 * a4 * a5 * a6 * a8 * a9 * a10 * a11)); [cancel|] end.
  assert (EQ: @field_at Noise.CS sh t_peer (DOT I._refcount) (Vint (p_refs P)) p =
              @field_at W_handshake_receive sh t_peer (DOT HC._refcount) (Vint (p_refs P)) p)
    by (apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  rewrite EQ, hrx5_B8RDc_kref. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite <- hrx5_B8RDc_kref, <- EQ. entailer!.
Qed.

End Wsec2.

(* ---------------------------------------------------------------------- *)
(* pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RDc_veqb x : veqb x x = true.
Proof. unfold veqb. rewrite if_true; reflexivity. Qed.

Lemma hrx5_B8RDc_bytes_eqb l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. rewrite if_true; reflexivity. Qed.

Lemma hrx5_B8RDc_pr_eqb P H : pr_eqb P (p_set_hs P H) = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb, p_set_hs. cbn [p_device p_dead p_cur p_prev p_next p_lsh p_id p_pknext p_cookie].
  rewrite !hrx5_B8RDc_veqb, !Int64.eq_true, !hrx5_B8RDc_bytes_eqb, !eqb_reflx. reflexivity.
Qed.

Lemma hrx5_B8RDc_peers_split i PS x : 0 <= i < Zlength PS ->
  peers_rep (upd_Znth i PS x) =
  peer_item_rep x * peers_rep (sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS).
Proof.
  intros Hi. rewrite upd_Znth_unfold by auto. unfold peers_rep. rewrite !iter_sepcon_app. simpl.
  apply pred_ext; cancel.
Qed.

Lemma hrx5_B8RDc_pknext_l l1 a sh P l2 head : pk_chain head (l1 ++ (a, sh, P) :: l2) ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 l2).
Proof.
  revert head; induction l1 as [|[[b shb] Q] l1 IH]; intros head H; simpl in H.
  - destruct H as [_ H]. destruct l2 as [|[[c shc] R] l2]; simpl in H.
    + left; exact H.
    + right. destruct H as [-> _]. left; reflexivity.
  - destruct H as [_ H]. exact (IH _ H).
Qed.

Lemma hrx5_B8RDc_pknext head PS i p sh P : pk_chain head PS -> 0 <= i < Zlength PS -> Znth i PS = (p, sh, P) ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 (sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS)).
Proof.
  intros H Hi E. rewrite (hrx5_B8RDc_split PS i Hi), E in H.
  destruct (hrx5_B8RDc_pknext_l _ _ _ _ _ _ H) as [H1|H1]; [left; exact H1|].
  right. rewrite map_app, in_app_iff. right; exact H1.
Qed.

(* ---------------------------------------------------------------------- *)
(* the node k <> i: its peer, the other peers, the table                   *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RDc_peers_at k PS : 0 <= k < Zlength PS ->
  peers_rep PS = peer_item_rep (Znth k PS) * peers_rep (sublist 0 k PS ++ sublist (k + 1) (Zlength PS) PS).
Proof.
  intros Hk. rewrite (hrx5_B8RDc_split PS k Hk) at 1. unfold peers_rep. rewrite !iter_sepcon_app. simpl.
  apply pred_ext; cancel.
Qed.

Lemma hrx5_B8RDc_upd_len j PS (x: val * share * peer) : 0 <= j < Zlength PS -> Zlength (upd_Znth j PS x) = Zlength PS.
Proof. intros Hj. apply upd_Znth_Zlength; auto. Qed.

Lemma hrx5_B8RDc_upd_nth j k PS (x: val * share * peer) : 0 <= j < Zlength PS -> 0 <= k < Zlength PS -> k <> j ->
  Znth k (upd_Znth j PS x) = Znth k PS.
Proof. intros Hj Hk Hn. apply upd_Znth_diff; auto. Qed.

Lemma hrx5_B8RDc_upd_map {B: Type} {dB: Inhabitant B} (f: val * share * peer -> B) j PS x : 0 <= j < Zlength PS ->
  f x = f (Znth j PS) -> map f (upd_Znth j PS x) = map f PS.
Proof.
  intros Hj Hf. pose proof (hrx5_B8RDc_upd_len j PS x Hj) as HL.
  apply Znth_eq_ext; [rewrite !Zlength_map; exact HL|].
  intros i Hi. rewrite Zlength_map, HL in Hi. rewrite !Znth_map by lia.
  destruct (Z.eq_dec i j) as [->|n].
  - rewrite upd_Znth_same by lia. apply Hf.
  - rewrite upd_Znth_diff by lia. reflexivity.
Qed.

Lemma hrx5_B8RDc_others_addrs j k PS a sh P : 0 <= j < Zlength PS -> a = peer_addr4 (Znth j PS) ->
  map peer_addr4 (sublist 0 k (upd_Znth j PS (a, sh, P)) ++
                  sublist (k + 1) (Zlength (upd_Znth j PS (a, sh, P))) (upd_Znth j PS (a, sh, P))) =
  map peer_addr4 (sublist 0 k PS ++ sublist (k + 1) (Zlength PS) PS).
Proof.
  intros Hj Ha. rewrite hrx5_B8RDc_upd_len by auto. rewrite !map_app, <- !sublist_map.
  rewrite (hrx5_B8RDc_upd_map peer_addr4) by (auto; rewrite Ha; reflexivity). reflexivity.
Qed.

Definition hrx5_B8RDc_shok (x: val * share * peer) : Prop := match x with (_, sh, _) => sh = Ews end.

Lemma hrx5_B8RDc_others_sh j k PS a P : 0 <= j < Zlength PS -> Forall hrx5_B8RDc_shok PS ->
  Forall (fun y => match y with (_, sh, _) => sh = Ews end)
    (sublist 0 k (upd_Znth j PS (a, Ews, P)) ++
     sublist (k + 1) (Zlength (upd_Znth j PS (a, Ews, P))) (upd_Znth j PS (a, Ews, P))).
Proof.
  intros Hj HF.
  set (g := fun x: val * share * peer => match x with (_, sh, _) => sh end).
  assert (Hgj: g (Znth j PS) = Ews).
  { assert (Hx: hrx5_B8RDc_shok (Znth j PS)) by (apply Forall_Znth; auto).
    destruct (Znth j PS) as [[b sh] Q]. exact Hx. }
  assert (E: map g (upd_Znth j PS (a, Ews, P)) = map g PS)
    by (apply (@hrx5_B8RDc_upd_map share Tsh); auto).
  assert (HC: Forall hrx5_B8RDc_shok (upd_Znth j PS (a, Ews, P))).
  { rewrite Forall_forall in HF |- *. intros x Hx.
    assert (Hg: In (g x) (map g PS)) by (rewrite <- E; apply in_map, Hx).
    apply in_map_iff in Hg. destruct Hg as (y & Ey & Hy). specialize (HF y Hy).
    destruct x as [[b sh] Q], y as [[c sh'] Q']. unfold hrx5_B8RDc_shok, g in *. congruence. }
  apply Forall_app; split; apply Forall_sublist; exact HC.
Qed.

Lemma hrx5_B8RDc_vremove_in a b l : b <> a -> (In b (vremove a l) <-> In b l).
Proof.
  intros H. induction l as [|x l IH]; simpl; [tauto|].
  destruct (EqDec_val x a) as [->|n]; simpl; rewrite IH; [|tauto].
  split; [auto|]. intros [E|E]; [congruence | exact E].
Qed.

Lemma hrx5_B8RDc_vin_remove a b l : b <> a -> vin b (vremove a l) = vin b l.
Proof.
  intros H. unfold vin. pose proof (hrx5_B8RDc_vremove_in a b l H) as E.
  destruct (in_dec eq_dec b (vremove a l)), (in_dec eq_dec b l); tauto.
Qed.

Lemma hrx5_B8RDc_entry_refl E : entry_eqb E E = true.
Proof. unfold entry_eqb. rewrite if_true by reflexivity. rewrite !Int.eq_true. reflexivity. Qed.

Lemma hrx5_B8RDc_hs_refl H : hs_eqb H H = true.
Proof.
  unfold hs_eqb. rewrite !Int.eq_true, Int64.eq_true, !hrx5_B8RDc_bytes_eqb. rewrite if_true by reflexivity.
  reflexivity.
Qed.

Lemma hrx5_B8RDc_snap T a q Q : hs_addr q <> a ->
  snap_eqb_nn (hs_snap_cur T q Q) (hs_snap_cur (t_remove T a) q Q) = true.
Proof.
  intros H. unfold hs_snap_cur, snap_of, snap_eqb_nn. cbn [sn_entry sn_hashed sn_hs].
  change (t_entry_d (t_remove T a) (hs_addr q)) with (t_entry_d T (hs_addr q)).
  cbn [t_remove t_L]. rewrite hrx5_B8RDc_vin_remove by auto.
  rewrite eqb_reflx, hrx5_B8RDc_entry_refl, hrx5_B8RDc_hs_refl. reflexivity.
Qed.

Lemma hrx5_B8RDc_pr_refl P : pr_eqb P P = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb.
  rewrite !hrx5_B8RDc_veqb, !Int64.eq_true, !hrx5_B8RDc_bytes_eqb, !eqb_reflx. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the lent objects                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RDc_peer_fc sh p P : peer_rep sh p P |-- !! @field_compatible Noise.CS t_peer [] p.
Proof. unfold peer_rep. entailer!. Qed.

Lemma hrx5_B8RDc_vo1 sh wg D : vobjs W_handshake_receive [VDev sh wg D] = device_rep sh wg D.
Proof. unfold vobjs. simpl. apply sepcon_emp. Qed.

(* ---------------------------------------------------------------------- *)
(* the pool of T (hrx5cr_pool), the table Tf                              *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RDc_F2_saddrs PS D : Forall2 hrx5cr_hs_ok PS D -> saddrs D = map (fun x => hs_addr (peer_addr4 x)) PS.
Proof.
  induction 1 as [|[[p s] P] [[b sh] E] PS D H _ IH]; [reflexivity|].
  destruct H as (-> & _). cbn [saddrs map] in *. unfold saddrs in IH. rewrite IH. reflexivity.
Qed.

Lemma hrx5_B8RDc_saddrs_skipn n (D: list (val * share * entry)) : saddrs (skipn n D) = skipn n (saddrs D).
Proof. unfold saddrs. revert D; induction n as [|n IH]; intros [|x D]; simpl; auto. Qed.

Lemma hrx5_B8RDc_ne KA PS T j k : hrx5cr_pool KA PS T -> NoDup (saddrs (t_D T)) ->
  0 <= j < Zlength PS -> 0 <= k < Zlength PS -> k <> j ->
  hs_addr (peer_addr4 (Znth k PS)) <> hs_addr (peer_addr4 (Znth j PS)).
Proof.
  intros [_ H2] Hnd Hj Hk Hn E.
  assert (Hnd2: NoDup (map (fun x => hs_addr (peer_addr4 x)) PS)).
  { rewrite <- (hrx5_B8RDc_F2_saddrs _ _ H2), hrx5_B8RDc_saddrs_skipn.
    rewrite <- (firstn_skipn (length KA) (saddrs (t_D T))) in Hnd. apply NoDup_app_remove_l in Hnd. exact Hnd. }
  apply Hn. apply (NoDup_Znth_inj _ k j Hnd2); rewrite ?Zlength_map; auto.
  rewrite !Znth_map by lia. exact E.
Qed.

Lemma hrx5_B8RDc_F2_in_l {A B: Type} (R: A -> B -> Prop) l1 l2 x :
  Forall2 R l1 l2 -> In x l1 -> exists y, In y l2 /\ R x y.
Proof.
  induction 1; simpl; [tauto|].
  intros [<-|HI]; [eauto|]. destruct (IHForall2 HI) as [z [? ?]]; eauto.
Qed.

Lemma hrx5_B8RDc_nodup_in (D: list (val * share * entry)) a s1 E1 s2 E2 :
  NoDup (saddrs D) -> In (a, s1, E1) D -> In (a, s2, E2) D -> E1 = E2.
Proof.
  induction D as [|[[x s] E] D IH]; [simpl; tauto|].
  cbn [saddrs map In]. intros Hnd H1 H2. inversion Hnd as [|? ? Hni Hnd']; subst.
  assert (Hin: forall s' E', In (a, s', E') D -> In a (saddrs D)).
  { intros s' E' H. unfold saddrs. apply in_map_iff. exists (a, s', E'). split; [reflexivity | exact H]. }
  destruct H1 as [H1|H1], H2 as [H2|H2].
  - inversion H1; inversion H2; subst; reflexivity.
  - inversion H1; subst. exfalso. exact (Hni (Hin _ _ H2)).
  - inversion H2; subst. exfalso. exact (Hni (Hin _ _ H1)).
  - exact (IH Hnd' H1 H2).
Qed.

Lemma hrx5_B8RDc_pool_hs KA PS T q sh Q : hrx5cr_pool KA PS T -> NoDup (saddrs (t_D T)) -> In (q, sh, Q) PS ->
  In (hs_addr q) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr q)) = q.
Proof.
  intros [_ H2] Hnd Hin.
  destruct (hrx5_B8RDc_F2_in_l _ _ _ _ H2 Hin) as ([[b sh'] E] & Hy & HP).
  destruct HP as (-> & _ & Hep & _).
  assert (HinD: In (hs_addr q, sh', E) (t_D T)).
  { rewrite <- (firstn_skipn (length KA) (t_D T)). apply in_or_app; right; exact Hy. }
  assert (Hs: In (hs_addr q) (saddrs (t_D T))).
  { unfold saddrs. apply in_map_iff. exists (hs_addr q, sh', E). split; [reflexivity | exact HinD]. }
  split; [exact Hs|].
  destruct (hrx5_B8RDc_sfind_in _ _ Hs) as (sh2 & E2 & Hf & Hin2).
  unfold t_entry_d, t_entry. rewrite Hf. rewrite (hrx5_B8RDc_nodup_in _ _ _ _ _ _ Hnd Hin2 HinD). exact Hep.
Qed.

Lemma hrx5_B8RDc_tD T Tf a : (Tf = T \/ Tf = t_remove T a) -> t_D Tf = t_D T.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma hrx5_B8RDc_entry_d T Tf a x : (Tf = T \/ Tf = t_remove T a) -> t_entry_d Tf x = t_entry_d T x.
Proof. intros H. unfold t_entry_d, t_entry. rewrite (hrx5_B8RDc_tD _ _ _ H). reflexivity. Qed.

Lemma hrx5_B8RDc_snapf T Tf a q Q : (Tf = T \/ Tf = t_remove T a) -> hs_addr q <> a ->
  snap_eqb_nn (hs_snap_cur T q Q) (hs_snap_cur Tf q Q) = true.
Proof.
  intros [-> | ->] H; [| apply hrx5_B8RDc_snap, H].
  unfold hs_snap_cur, snap_of, snap_eqb_nn. cbn [sn_entry sn_hashed sn_hs].
  rewrite eqb_reflx, hrx5_B8RDc_entry_refl, hrx5_B8RDc_hs_refl. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the objects lent to pr_same: the device, the other peers (pubkey_next); *)
(* the keypair slots are NULL (hrx5_pok)                                    *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8RDc_VO (wg: val) (D: device) (others: list (val * share * peer)) : list vobj :=
  [VDev Tsh wg D; VPeers others].

Lemma hrx5_B8RDc_vo2 wg D others :
  vobjs W_handshake_receive (hrx5_B8RDc_VO wg D others) = (device_rep Tsh wg D * peers_rep others)%logic.
Proof. unfold vobjs, hrx5_B8RDc_VO. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hrx5_B8RDc_vp p wg D others P :
  p_device P = wg -> p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 others) ->
  Forall (vp_ok (p :: vobjs_addrs (hrx5_B8RDc_VO wg D others))) (pr_ptrs P P).
Proof.
  intros Hd Hc Hp Hn Hpk.
  assert (E: vobjs_addrs (hrx5_B8RDc_VO wg D others) = [wg; id_addr wg; cc_addr wg] ++ map peer_addr4 others).
  { unfold vobjs_addrs, hrx5_B8RDc_VO. simpl. rewrite app_nil_r. reflexivity. }
  rewrite E. clear E.
  set (A := p :: [wg; id_addr wg; cc_addr wg] ++ map peer_addr4 others).
  assert (Hdv: vp_ok A (p_device P)) by (right; subst A; right; rewrite Hd; left; reflexivity).
  assert (Hpv: vp_ok A (p_pknext P)).
  { destruct Hpk as [Hpk|Hpk]; [left; exact Hpk|].
    right. subst A. right. rewrite in_app_iff. right. exact Hpk. }
  unfold pr_ptrs. rewrite Hc, Hp, Hn.
  repeat apply Forall_cons; try apply Forall_nil; auto; left; reflexivity.
Qed.
