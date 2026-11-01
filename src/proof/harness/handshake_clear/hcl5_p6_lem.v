(*
   - accessors (P |-- Q * (Q -* P)) for the target node (ONE value at the world W: hcl5_p6_nv), its snapshot field
     (HCS, for hs_zeroed_from) and rest field (CKS, for pr_same), the cleared peer's handshake entry in the index
     table (at W, for the loads of h->entry fields), the peer's reference count (at W);
   - pure facts: the snapshot vs the cleared handshake (zeroed_from = true), the removed entry (not hashed, next
     NULL), pr_eqb of a peer and its cleared self, the lent objects' addresses. *)
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
Local Open Scope logic.

#[export] Instance hcl5_p6_cceN : change_composite_env Noise.CS W_handshake_clear.
Proof. make_cs_preserve Noise.CS W_handshake_clear. Defined.
#[export] Instance hcl5_p6_cceH : change_composite_env HCS W_handshake_clear.
Proof. make_cs_preserve HCS W_handshake_clear. Defined.
#[export] Instance hcl5_p6_cceK : change_composite_env CKS W_handshake_clear.
Proof. make_cs_preserve CKS W_handshake_clear. Defined.

(* ---------------------------------------------------------------------- *)
(* accessors                                                               *)
(* ---------------------------------------------------------------------- *)

Definition hcl5_p6_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hcl5_p6_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hcl5_p6_acc_refl Q : hcl5_p6_acc Q Q.
Proof.
  unfold hcl5_p6_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hcl5_p6_acc_eq Q A : Q = A -> hcl5_p6_acc Q A.
Proof. intros ->. apply hcl5_p6_acc_refl. Qed.

Lemma hcl5_p6_acc_l Q A F : hcl5_p6_acc Q A -> hcl5_p6_acc Q (A * F).
Proof.
  unfold hcl5_p6_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hcl5_p6_acc_r Q A F : hcl5_p6_acc Q A -> hcl5_p6_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hcl5_p6_acc_l, H. Qed.

Lemma hcl5_p6_acc_prop Q (c: Prop) A : (c -> hcl5_p6_acc Q A) -> hcl5_p6_acc Q (!! c && A).
Proof.
  unfold hcl5_p6_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcl5_p6_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hcl5_p6_acc Q (A x)) -> hcl5_p6_acc Q (EX x, A x).
Proof.
  unfold hcl5_p6_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

Lemma hcl5_p6_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hcl5_p6_acc Q A) -> hcl5_p6_acc Q A.
Proof.
  unfold hcl5_p6_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hcl5_p6_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hcl5_p6_acc Q (f x) -> hcl5_p6_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hcl5_p6_acc_l, H | apply hcl5_p6_acc_r, IH, Hin].
Qed.

Lemma hcl5_p6_acc_trans Q B P : hcl5_p6_acc Q B -> hcl5_p6_acc B P -> hcl5_p6_acc Q P.
Proof.
  unfold hcl5_p6_acc. intros H1 H2. eapply derives_trans; [exact H2|].
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

(* the node of peer p with the snapshot sn, the count r, the rest of P, the link nx: ONE value at W *)
Definition hcl5_p6_nv (p: val) (sn: hsnap) (r: int) (P: peer) (nx: val) : @reptype W_handshake_clear t_hnode4 :=
  (p, (hsnap_val sn, (Vint r, (prsnap_val P, nx)))).

Lemma hcl5_p6_head l NS : hnodes_rep4 W l NS |-- !! (l = hcl5_head NS).
Proof. destruct NS as [|N NS]; simpl; entailer!. Qed.

Lemma hcl5_p6_c6 NS1 N NS2 l :
  hcl5_p6_acc (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hcl5_head NS2)))) (hn_addr N))
    (hnodes_rep4 W l (NS1 ++ N :: NS2)).
Proof.
  revert l; induction NS1 as [|M NS1 IH]; intros l; simpl.
  - apply hcl5_p6_acc_prop; intros ->. apply hcl5_p6_acc_ex; intros nx.
    apply hcl5_p6_acc_pure with (c := nx = hcl5_head NS2).
    { sep_apply (hcl5_p6_head nx NS2). entailer!. }
    intros ->. do 2 apply hcl5_p6_acc_l. apply hcl5_p6_acc_r, hcl5_p6_acc_refl.
  - apply hcl5_p6_acc_prop; intros _. apply hcl5_p6_acc_ex; intros nx.
    apply hcl5_p6_acc_r, IH.
Qed.

Lemma hcl5_p6_KW sh (v: @reptype CKS t_hnode4) x :
  @data_at CKS sh t_hnode4 v x = @data_at W_handshake_clear sh t_hnode4 v x.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hcl5_p6_split {A: Type} {d: Inhabitant A} (l: list A) i : 0 <= i < Zlength l ->
  l = sublist 0 i l ++ Znth i l :: sublist (i + 1) (Zlength l) l.
Proof.
  intros Hi. rewrite <- (sublist_same 0 (Zlength l) l) at 1 by auto.
  rewrite (sublist_split 0 i (Zlength l)) by lia. rewrite (sublist_split i (i + 1) (Zlength l)) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma hcl5_p6_len_peers NS PS : hnodes_peers4 NS PS -> Zlength NS = Zlength PS.
Proof.
  unfold hnodes_peers4. intros E. rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS), E.
  reflexivity.
Qed.

Lemma hcl5_p6_hn_p NS PS i : hnodes_peers4 NS PS -> 0 <= i < Zlength NS ->
  hn_p (Znth i NS) = peer_addr4 (Znth i PS).
Proof.
  intros E Hi. pose proof (hcl5_p6_len_peers _ _ E) as HL.
  rewrite <- (Znth_map i hn_p NS) by lia. rewrite <- (Znth_map i peer_addr4 PS) by lia.
  unfold hnodes_peers4 in E. rewrite E. reflexivity.
Qed.

Lemma hcl5_p6_snapped_len T NS PS : hnodes_peers4 NS PS -> Zlength (hnodes_snapped4 T NS PS) = Zlength NS.
Proof.
  intros E. pose proof (hcl5_p6_len_peers _ _ E) as HL. unfold hnodes_snapped4.
  rewrite Zlength_map. rewrite !Zlength_correct in *. rewrite combine_length. f_equal. lia.
Qed.

Lemma hcl5_p6_snapped_nth T NS PS i : hnodes_peers4 NS PS -> 0 <= i < Zlength NS ->
  Znth i (hnodes_snapped4 T NS PS) = hn_snapshot4 T (Znth i NS) (Znth i PS).
Proof.
  intros E Hi. pose proof (hcl5_p6_len_peers _ _ E) as HL. unfold hnodes_snapped4.
  rewrite Znth_map.
  2:{ rewrite !Zlength_correct in *. rewrite combine_length. lia. }
  rewrite Znth_combine by auto. reflexivity.
Qed.

Lemma hcl5_p6_snapped_head T NS PS : hnodes_peers4 NS PS -> hcl5_head (hnodes_snapped4 T NS PS) = hcl5_head NS.
Proof.
  intros E. pose proof (hcl5_p6_len_peers _ _ E) as HL.
  destruct NS as [|N NS]; [reflexivity|]. destruct PS as [|[[a sh] P] PS].
  { rewrite Zlength_cons, Zlength_nil in HL. pose proof (Zlength_nonneg NS). lia. }
  reflexivity.
Qed.

(* the target node out of the list, at W *)
Lemma hcl5_p6_node_open T NS PS i p sh P : hnodes_peers4 NS PS -> 0 <= i < Zlength NS -> Znth i PS = (p, sh, P) ->
  hnodes_rep4 W (hcl5_head NS) (hnodes_snapped4 T NS PS) |--
  EX nx: val,
    @data_at W_handshake_clear Ews t_hnode4 (hcl5_p6_nv p (hs_snap_cur T p P) (p_refs P) P nx) (hn_addr (Znth i NS)) *
    (@data_at W_handshake_clear Ews t_hnode4 (hcl5_p6_nv p (hs_snap_cur T p P) (p_refs P) P nx) (hn_addr (Znth i NS)) -*
     hnodes_rep4 W (hcl5_head NS) (hnodes_snapped4 T NS PS)).
Proof.
  intros E Hi EP.
  pose proof (hcl5_p6_snapped_len T _ _ E) as HL.
  pose proof (hcl5_p6_snapped_nth T _ _ i E Hi) as HN. rewrite EP in HN.
  pose proof (hcl5_p6_hn_p _ _ i E Hi) as Hp. rewrite EP in Hp. cbn [peer_addr4] in Hp.
  set (NS' := hnodes_snapped4 T NS PS) in *. clearbody NS'.
  assert (Hi': 0 <= i < Zlength NS') by lia.
  pose proof (hcl5_p6_split NS' i Hi') as HS.
  set (NS2 := sublist (i + 1) (Zlength NS') NS') in *. clearbody NS2.
  set (NS1 := sublist 0 i NS') in *. clearbody NS1.
  rewrite HN in HS. clear HN. rewrite HS.
  eapply derives_trans; [apply hcl5_p6_c6|]. cbn [hn_p hn_snap hn_refs hn_rest hn_addr hn_snapshot4].
  Exists (hcl5_head NS2). rewrite hcl5_p6_KW. rewrite Hp. unfold hcl5_p6_nv. apply derives_refl.
Qed.

(* the snapshot field of a node (HCS), the rest field (CKS) *)
Lemma hcl5_p6_HW sh (v: @reptype HCS t_hsnap) y :
  @data_at HCS sh t_hsnap v y = @data_at W_handshake_clear sh t_hsnap v y.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hcl5_p6_PW sh (v: @reptype CKS t_prsnap) y :
  @data_at CKS sh t_prsnap v y = @data_at W_handshake_clear sh t_prsnap v y.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Section Wsec.
#[local] Existing Instance W_handshake_clear.

Lemma hcl5_p6_node_snap sh p sn r P nx x :
  data_at sh t_hnode4 (hcl5_p6_nv p sn r P nx) x |--
  @data_at HCS sh t_hsnap (hsnap_val sn) (field_address t_hnode4 [StructField HC._snap] x) *
  (@data_at HCS sh t_hsnap (hsnap_val sn) (field_address t_hnode4 [StructField HC._snap] x) -*
   data_at sh t_hnode4 (hcl5_p6_nv p sn r P nx) x).
Proof.
  unfold hcl5_p6_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._snap) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives.
  - rewrite field_at_data_at. rewrite hcl5_p6_HW. apply derives_refl.
  - apply (allp_left _ (hsnap_val sn)). apply wand_derives.
    + rewrite field_at_data_at. rewrite hcl5_p6_HW. apply derives_refl.
    + apply derives_refl.
Qed.

Lemma hcl5_p6_node_rest sh p sn r P nx x :
  data_at sh t_hnode4 (hcl5_p6_nv p sn r P nx) x |--
  @data_at CKS sh t_prsnap (prsnap_val P) (field_address t_hnode4 [StructField HC._rest] x) *
  (@data_at CKS sh t_prsnap (prsnap_val P) (field_address t_hnode4 [StructField HC._rest] x) -*
   data_at sh t_hnode4 (hcl5_p6_nv p sn r P nx) x).
Proof.
  unfold hcl5_p6_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._rest) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives.
  - rewrite field_at_data_at. rewrite hcl5_p6_PW. apply derives_refl.
  - apply (allp_left _ (prsnap_val P)). apply wand_derives.
    + rewrite field_at_data_at. rewrite hcl5_p6_PW. apply derives_refl.
    + apply derives_refl.
Qed.

Lemma hcl5_p6_node_p sh p sn r P nx x :
  data_at sh t_hnode4 (hcl5_p6_nv p sn r P nx) x |--
  field_at sh t_hnode4 [StructField HC._p] p x *
  (field_at sh t_hnode4 [StructField HC._p] p x -* data_at sh t_hnode4 (hcl5_p6_nv p sn r P nx) x).
Proof.
  unfold hcl5_p6_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._p) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p). apply derives_refl.
Qed.

Lemma hcl5_p6_node_refs sh p sn r P nx x :
  data_at sh t_hnode4 (hcl5_p6_nv p sn r P nx) x |--
  field_at sh t_hnode4 [StructField HC._refs] (Vint r) x *
  (field_at sh t_hnode4 [StructField HC._refs] (Vint r) x -* data_at sh t_hnode4 (hcl5_p6_nv p sn r P nx) x).
Proof.
  unfold hcl5_p6_nv.
  eapply derives_trans; [apply andp_right; [apply data_at_local_facts | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [eapply (gfield_ramif sh t_hnode4 [] (StructField HC._refs) _ _ x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ (Vint r)). apply derives_refl.
Qed.

End Wsec.

(* ---------------------------------------------------------------------- *)
(* the index table: the removed entry, at W                                *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p6_sfind_in (D: list (val * share * entry)) a : In a (saddrs D) ->
  exists sh E, sfind D a = Some (sh, E) /\ In (a, sh, E) D.
Proof.
  induction D as [|[[x sh] v] D IH]; intros H; [destruct H|].
  cbn [saddrs map sfind] in *. destruct (eq_dec x a) as [->|n].
  - exists sh, v; split; [reflexivity | left; reflexivity].
  - destruct H as [H|H]; [congruence|]. destruct (IH H) as (sh' & E & H1 & H2).
    exists sh', E; split; [exact H1 | right; exact H2].
Qed.

Lemma hcl5_p6_vremove_notin a l : ~ In a (vremove a l).
Proof.
  induction l as [|x l IH]; simpl; [auto|]. destruct (EqDec_val x a) as [->|n]; [exact IH|].
  intros [H|H]; [congruence | exact (IH H)].
Qed.

Lemma hcl5_p6_succ_notin a l : ~ In a l -> succ_in l a = nullval.
Proof.
  induction l as [|x l IH]; simpl; [auto|]. intros H. destruct (EqDec_val x a) as [->|n].
  - exfalso; apply H; left; reflexivity.
  - apply IH. intros H'; apply H; right; exact H'.
Qed.

Lemma hcl5_p6_vin_false a l : ~ In a l -> vin a l = false.
Proof. intros H. unfold vin. destruct (in_dec eq_dec a l); [contradiction | reflexivity]. Qed.

Lemma hcl5_p6_vin_true a l : vin a l = false -> ~ In a l.
Proof. unfold vin. destruct (in_dec eq_dec a l); [discriminate | auto]. Qed.

Lemma hcl5_p6_fc_hs p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_handshake_clear t_hs [StructField HCL5._entry] (hs_addr p).
Proof.
  intros FC.
  assert (FCW: @field_compatible W_handshake_clear t_peer [] p).
  { apply (@field_compatible_change_composite Noise.CS W_handshake_clear _); [prove_cs_preserve_type | exact FC]. }
  assert (H1: @field_compatible W_handshake_clear t_peer [StructField HCL5._entry; StructField HCL5._handshake] p)
    by auto with field_compatible.
  assert (E: hs_addr p = @field_address W_handshake_clear t_peer [StructField HCL5._handshake] p).
  { rewrite field_address_offset by auto with field_compatible. reflexivity. }
  rewrite E. exact (field_compatible_app [StructField HCL5._entry] t_peer [StructField HCL5._handshake] p H1).
Qed.

Lemma hcl5_p6_entry_W sh p E nx hb : @field_compatible Noise.CS t_peer [] p ->
  entry_at sh (hs_addr p) E nx hb =
  @field_at W_handshake_clear sh t_hs [StructField HCL5._entry] (entry_val E nx hb) (hs_addr p).
Proof.
  intros FC. pose proof (hcl5_p6_fc_hs p FC) as FCh.
  unfold entry_at.
  rewrite (@data_at_change_composite Noise.CS W_handshake_clear _ sh t_entry_s _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite field_at_data_at, field_address_offset by auto.
  rewrite isptr_offset_val_zero; [reflexivity|].
  destruct FCh as [Hp _]. exact Hp.
Qed.

Lemma hcl5_p6_itab_open sht tab T p : @field_compatible Noise.CS t_peer [] p ->
  In (hs_addr p) (saddrs (t_D T)) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  hcl5_p6_acc (@field_at W_handshake_clear Ews t_hs [StructField HCL5._entry]
                 (entry_val (t_entry_d T (hs_addr p)) nullval false) (hs_addr p))
    (itable sht tab (t_remove T (hs_addr p))).
Proof.
  intros FC Hin Hsh. destruct (hcl5_p6_sfind_in _ _ Hin) as (sh & E & Hf & Hi).
  assert (Esh: sh = Ews) by (rewrite Forall_forall in Hsh; exact (Hsh _ Hi)). subst sh.
  assert (EE: t_entry_d T (hs_addr p) = E) by (unfold t_entry_d, t_entry; rewrite Hf; reflexivity).
  rewrite EE. unfold itable. apply hcl5_p6_acc_prop; intros _. apply hcl5_p6_acc_r.
  apply (hcl5_p6_acc_iter _ _ (hs_addr p, Ews, E)); [exact Hi|].
  cbn [pool_item_rep t_remove t_L t_D].
  rewrite hcl5_p6_succ_notin, hcl5_p6_vin_false by apply hcl5_p6_vremove_notin.
  rewrite hcl5_p6_entry_W by exact FC. apply hcl5_p6_acc_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* the peer: its reference count at W                                      *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p6_peer_refs sh p P :
  hcl5_p6_acc (@field_at W_handshake_clear sh t_peer [StructField HCL5._refcount] (Vint (p_refs P)) p)
    (peer_rep sh p P).
Proof.
  unfold peer_rep. apply hcl5_p6_acc_prop; intros _.
  do 4 apply hcl5_p6_acc_l. apply hcl5_p6_acc_r. apply hcl5_p6_acc_eq.
  rewrite (@field_at_change_composite Noise.CS W_handshake_clear _ sh t_peer [StructField I._refcount]
    (Vint (p_refs P)) (Vint (p_refs P)) (JMeq_refl _)) by prove_cs_preserve_type.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p6_zeroed T T' a E H :
  zeroed_from (snap_of T a E H) (snap_of T' a E (hs_zero H)) = true.
Proof.
  unfold zeroed_from, snap_of, hs_zero, is_zero, bytes_eqb;
    cbn [sn_hs sn_entry hs_state hs_rindex hs_eph hs_reph hs_hash hs_ck hs_lic hs_sid hs_rstatic hs_ss hs_psk hs_ts].
  rewrite !Int.eq_true, Int64.eq_true.
  repeat (rewrite if_true by (try reflexivity; try (rewrite Zlength_zeros; reflexivity))).
  reflexivity.
Qed.

Lemma hcl5_p6_veqb x : veqb x x = true.
Proof. unfold veqb. rewrite if_true; reflexivity. Qed.

Lemma hcl5_p6_bytes_eqb l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. rewrite if_true; reflexivity. Qed.

Lemma hcl5_p6_pr_eqb P H : pr_eqb P (p_set_hs P H) = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb, p_set_hs. cbn [p_device p_dead p_cur p_prev p_next p_lsh p_id p_pknext p_cookie].
  rewrite !hcl5_p6_veqb, !Int64.eq_true, !hcl5_p6_bytes_eqb, !eqb_reflx. reflexivity.
Qed.

Lemma hcl5_p6_peers_split i PS x : 0 <= i < Zlength PS ->
  peers_rep (upd_Znth i PS x) =
  peer_item_rep x * peers_rep (sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS).
Proof.
  intros Hi. rewrite upd_Znth_unfold by auto. unfold peers_rep. rewrite !iter_sepcon_app. simpl.
  apply pred_ext; cancel.
Qed.

Lemma hcl5_p6_pknext_l l1 a sh P l2 head : pk_chain head (l1 ++ (a, sh, P) :: l2) ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 l2).
Proof.
  revert head; induction l1 as [|[[b shb] Q] l1 IH]; intros head H; simpl in H.
  - destruct H as [_ H]. destruct l2 as [|[[c shc] R] l2]; simpl in H.
    + left; exact H.
    + right. destruct H as [-> _]. left; reflexivity.
  - destruct H as [_ H]. exact (IH _ H).
Qed.

Lemma hcl5_p6_pknext head PS i p sh P : pk_chain head PS -> 0 <= i < Zlength PS -> Znth i PS = (p, sh, P) ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 (sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS)).
Proof.
  intros H Hi E. rewrite (hcl5_p6_split PS i Hi), E in H.
  destruct (hcl5_p6_pknext_l _ _ _ _ _ _ H) as [H1|H1]; [left; exact H1|].
  right. rewrite map_app, in_app_iff. right; exact H1.
Qed.
