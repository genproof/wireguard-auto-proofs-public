(* law handshake_clear: main's phase P5, statements 9..15: target = hnodes_pick(peers); hnodes_snap(peers); kents_snap(kes); dev_take(&ds, &w); shim_take(&ss); h = &target->p->handshake; wg_noise_handshake_clear(h).
   (states: hcl5_defs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

#[local] Instance hcl5_p5_cceN : change_composite_env Noise.CS W_handshake_clear.
Proof. make_cs_preserve Noise.CS W_handshake_clear. Defined.
#[local] Instance hcl5_p5_cceK : change_composite_env CKS W_handshake_clear.
Proof. make_cs_preserve CKS W_handshake_clear. Defined.

Section hcl5_p5_helpers.
Local Open Scope logic.
(* ---- accessors: P |-- Q * (Q -* P) ---- *)
Definition hcl5_p5_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hcl5_p5_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hcl5_p5_acc_refl Q : hcl5_p5_acc Q Q.
Proof.
  unfold hcl5_p5_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hcl5_p5_acc_eq Q A : Q = A -> hcl5_p5_acc Q A.
Proof. intros ->. apply hcl5_p5_acc_refl. Qed.

Lemma hcl5_p5_acc_l Q A F : hcl5_p5_acc Q A -> hcl5_p5_acc Q (A * F).
Proof.
  unfold hcl5_p5_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hcl5_p5_acc_r Q A F : hcl5_p5_acc Q A -> hcl5_p5_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hcl5_p5_acc_l, H. Qed.

Lemma hcl5_p5_acc_prop Q (c: Prop) A : (c -> hcl5_p5_acc Q A) -> hcl5_p5_acc Q (!! c && A).
Proof.
  unfold hcl5_p5_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcl5_p5_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hcl5_p5_acc Q (A x)) -> hcl5_p5_acc Q (EX x, A x).
Proof.
  unfold hcl5_p5_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

Lemma hcl5_p5_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hcl5_p5_acc Q A) -> hcl5_p5_acc Q A.
Proof.
  unfold hcl5_p5_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hcl5_p5_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hcl5_p5_acc Q (f x) -> hcl5_p5_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hcl5_p5_acc_l, H | apply hcl5_p5_acc_r, IH, Hin].
Qed.

(* the node's field p, at the world *)
Lemma hcl5_p5_node_split p sn r rs nx x :
  @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x |--
  @field_at W Ews t_hnode4 [StructField HC._p] p x *
  (@field_at W Ews t_hnode4 [StructField HC._p] p x -* @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x).
Proof.
  rewrite <- (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HC._p] p p (JMeq_refl p))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  (eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) _ p x); [apply JMeq_refl | auto with field_compatible] |]).
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p).
  apply derives_refl.
Qed.

Lemma hcl5_p5_node_acc l NS N : In N NS ->
  hcl5_p5_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N)) (hnodes_rep4 W l NS).
Proof.
  revert l; induction NS as [|N0 NS IH]; intros l Hin; [destruct Hin|]. cbn [hnodes_rep4].
  apply hcl5_p5_acc_prop; intros Hl. apply hcl5_p5_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hcl5_p5_acc_l, hcl5_p5_acc_l, hcl5_p5_acc_r. apply hcl5_p5_node_split.
  - apply hcl5_p5_acc_r, IH, Hin.
Qed.

Lemma hcl5_p5_acc_trans Q B P : hcl5_p5_acc Q B -> hcl5_p5_acc B P -> hcl5_p5_acc Q P.
Proof.
  unfold hcl5_p5_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

End hcl5_p5_helpers.

Lemma hcl5_p5_ptrs PS : peers_rep PS |-- !! Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  induction PS as [| [[a sh] P] PS IH]; unfold peers_rep in *; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_item_rep at 1, peer_rep. entailer!.
    constructor; [cbn; destruct H0; assumption | assumption].
Qed.

(* ---- pointers ---- *)
Lemma hcl5_p5_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
    match goal with X: field_compatible _ _ (hn_addr N) |- _ => destruct X as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hcl5_p5_kptrs l KE : kents_rep W l KE |-- !! Forall (fun e => isptr (ke_addr e)) KE.
Proof.
  revert l; induction KE as [| e KE IH]; intros l; cbn [kents_rep].
  - entailer!.
  - Intros nx. sep_apply (IH nx). unfold kent_cell. entailer!.
    constructor; [| assumption].
    match goal with X: field_compatible t_kent [] (ke_addr e) |- _ => destruct X; assumption end.
Qed.

(* ---- pure facts ---- *)
Lemma hcl5_p5_pknext head PS : pk_chain head PS -> Forall (fun x => isptr (peer_addr4 x)) PS ->
  Forall (fun x => match x with (_, _, P) => p_pknext P <> Vundef end) PS.
Proof.
  revert head; induction PS as [| [[a sh] P] PS IH]; intros head Hc Hp; constructor.
  - cbn in Hc. destruct Hc as [_ Hc]. destruct PS as [| [[b sh'] P'] PS'].
    + cbn in Hc. rewrite Hc. discriminate.
    + cbn in Hc. destruct Hc as [-> _]. inversion Hp; subst. inversion H2; subst. cbn in *.
      destruct b; try contradiction; discriminate.
  - cbn in Hc. destruct Hc as [_ Hc]. inversion Hp; subst. eapply IH; eauto.
Qed.

Section hcl5_p5_pure.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_p5_snap_pre L head PS KE T :
  Forall (hcl5_pok L) PS -> pk_chain head PS -> hcl5_T_ok PS KE T -> hcl5_slots_ok KE PS ->
  Forall (fun x => isptr (peer_addr4 x)) PS -> Forall (fun e => isptr (ke_addr e)) KE -> isptr (l_w L) ->
  Forall (fun x => match x with (p, _, P) =>
            In (hs_addr p) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr p)) <> Vundef /\
            hs_sid (p_hs P) <> Vundef /\
            Forall (fun v => v <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P] end) PS.
Proof.
  intros Hpok Hch (HT1 & HT2 & HT3 & HT4) Hsl Hptr Hkp Hwb. unfold hcl5_slots_ok in Hsl.
  pose proof (hcl5_p5_pknext head PS Hch Hptr) as Hpkn.
  rewrite Forall_forall in Hpok, HT3, Hsl, Hptr, Hkp, Hpkn |- *. intros [[p sh] P] Hin.
  pose proof (Hptr _ Hin) as Hp. cbn in Hp.
  destruct (Hpok _ Hin) as (_ & Hdev & Hsid & _ & _).
  pose proof (HT3 _ Hin) as He. cbn in He.
  pose proof (Hsl _ Hin) as Hs. cbn in Hs.
  pose proof (Hpkn _ Hin) as Hpk. cbn in Hpk.
  assert (Hk: forall k, k = nullval \/ In k (map ke_addr KE) -> k <> Vundef).
  { intros k [-> | Hk]; [discriminate|]. apply in_map_iff in Hk. destruct Hk as (e & <- & He').
    specialize (Hkp _ He'). destruct (ke_addr e); try contradiction; discriminate. }
  rewrite Forall_forall in Hs.
  split; [| split; [| split]].
  - rewrite HT1. apply in_or_app. right. apply in_map_iff. exists (p, sh, P). split; [reflexivity | exact Hin].
  - rewrite He. destruct p; try contradiction; discriminate.
  - rewrite Hsid. unfold id_addr. destruct (l_w L); try contradiction; discriminate.
  - repeat constructor.
    + rewrite Hdev. destruct (l_w L); try contradiction; discriminate.
    + apply Hk, Hs; cbn; auto.
    + apply Hk, Hs; cbn; auto.
    + apply Hk, Hs; cbn; auto.
    + exact Hpk.
Qed.

Lemma hcl5_p5_ksnap_pre PS KE T :
  hcl5_T_ok PS KE T -> Forall (fun x => isptr (peer_addr4 x)) PS ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ e_peer (t_entry_d T (ke_addr e)) <> Vundef) KE.
Proof.
  intros (HT1 & HT2 & HT3 & HT4) Hptr. rewrite Forall_forall in HT4, Hptr |- *. intros e He. split.
  - rewrite HT1. apply in_or_app. left. apply in_map, He.
  - specialize (HT4 _ He). apply in_map_iff in HT4. destruct HT4 as (x & Hx & Hx'). rewrite <- Hx.
    specialize (Hptr _ Hx'). destruct (peer_addr4 x); try contradiction; discriminate.
Qed.

Lemma hcl5_p5_head head PS : pk_chain head PS -> Forall (fun x => isptr (peer_addr4 x)) PS -> head <> Vundef.
Proof.
  destruct PS as [| [[a sh] P] PS]; cbn; intros Hc Hp.
  - subst; discriminate.
  - destruct Hc as [-> _]. inversion Hp; subst. cbn in *. destruct a; try contradiction; discriminate.
Qed.
End hcl5_p5_pure.

Lemma hcl5_p5_sfind {A: Type} (l: list (val * share * A)) a :
  In a (saddrs l) -> exists sh E, sfind l a = Some (sh, E).
Proof.
  induction l as [| [[x sh] v] l IH]; cbn; [tauto|]. intros Hin.
  match goal with |- context [if ?c then _ else _] => destruct c as [<- | Hne] end; [eauto|].
  destruct Hin as [-> | Hin]; [contradiction | apply IH, Hin].
Qed.

Lemma hcl5_p5_inpool PS KE T x : hcl5_T_ok PS KE T -> In x PS -> hs_in_pool T (peer_addr4 x).
Proof.
  intros (H1 & _ & H3 & _) Hin. unfold hs_in_pool.
  assert (Ha: In (hs_addr (peer_addr4 x)) (saddrs (t_D T)))
    by (rewrite H1; apply in_or_app; right; apply (in_map (fun y => hs_addr (peer_addr4 y))), Hin).
  destruct (hcl5_p5_sfind _ _ Ha) as (sh & E & HE).
  exists E. unfold t_entry; rewrite HE. split; [reflexivity|].
  rewrite Forall_forall in H3. specialize (H3 _ Hin). unfold t_entry_d, t_entry in H3. rewrite HE in H3. exact H3.
Qed.

Lemma hcl5_p5_snapped_in T NS PS i : Zlength NS = Zlength PS -> 0 <= i < Zlength NS ->
  exists N, In N (hnodes_snapped4 T NS PS) /\ hn_addr N = hn_addr (Znth i NS) /\ hn_p N = hn_p (Znth i NS).
Proof.
  revert PS i; induction NS as [| N0 NS IH]; intros PS i Hl Hi; [rewrite Zlength_nil in Hi; lia|].
  destruct PS as [| x PS]; [rewrite Zlength_nil, Zlength_cons in Hl; rep_lia|].
  rewrite !Zlength_cons in Hl. rewrite Zlength_cons in Hi.
  unfold hnodes_snapped4. cbn [combine map].
  destruct (Z.eq_dec i 0) as [-> | Hne].
  - exists (hn_snapshot4 T N0 x). rewrite Znth_0_cons. split; [left; reflexivity|].
    destruct x as [[p sh] P]; split; reflexivity.
  - rewrite Znth_pos_cons by lia.
    destruct (IH PS (i - 1)) as (N & HN & HA & HP); [lia | lia |].
    exists N. split; [right; exact HN | split; assumption].
Qed.

Lemma hcl5_p5_split PS i : 0 <= i < Zlength PS ->
  peers_rep PS =
  (peer_item_rep (Znth i PS) * iter_sepcon peer_item_rep (sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS))%logic.
Proof.
  intros Hi. unfold peers_rep.
  rewrite <- (upd_Znth_triv i PS (Znth i PS)) at 1 by (auto; lia).
  rewrite upd_Znth_unfold by lia. rewrite !iter_sepcon_app. cbn [iter_sepcon].
  apply pred_ext; cancel.
Qed.

Lemma hcl5_p5_split_upd PS i v : 0 <= i < Zlength PS ->
  peers_rep (upd_Znth i PS v) =
  (peer_item_rep v * iter_sepcon peer_item_rep (sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS))%logic.
Proof.
  intros Hi. unfold peers_rep. rewrite upd_Znth_unfold by lia. rewrite !iter_sepcon_app. cbn [iter_sepcon].
  apply pred_ext; cancel.
Qed.

Section P5.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_P5_ok {Espec: OracleKind} gv L FR :
  hcl5_hyps x25519 ->
  semax (hcl5_Delta x25519) (hcl5_SK x25519 gv L FR) hcl5_P5
    (overridePost (hcl5_S5 x25519 gv L FR) (hcl5_R gv)).
Proof.
  intros HH. unfold hcl5_SK, hcl5_Delta, hcl5_R, hcl5_P5. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head KE.
  unfold hcl5_lvars, hcl5_scr, hcl5_world, hcl5_globs, hcl5_snaps0; cbn [app].
  pose proof H0 as Hinv. destruct Hinv as (Hpok & Hwf & Hch & Hnp & HT & Hsl).
  assert_PROP (Forall (fun x => isptr (peer_addr4 x)) PS) as Hptr by (sep_apply (hcl5_p5_ptrs PS); entailer!).
  assert_PROP (Forall (fun e => isptr (ke_addr e)) KE) as Hkp by (sep_apply (hcl5_p5_kptrs (hcl5_khead KE) KE); entailer!).
  assert_PROP (is_pointer_or_null (hcl5_head NS)) as Hpn by (sep_apply (hcl5_p5_pn (hcl5_head NS) NS); entailer!).
  assert_PROP (isptr (l_w L) /\ isptr (l_pt L) /\ isptr (l_it L)) as Hlv by entailer!.
  destruct Hlv as (Hwb & Hpt & Hit).
  forward.
  forward_call (hcl5_head NS, NS). Intros i.
  forward.
  forward.
  forward_call (hcl5_head NS, NS, PS, Tsh, l_it L, T).
  { apply (hcl5_p5_snap_pre L head PS KE T Hpok Hch HT Hsl Hptr Hkp Hwb). }
  forward_call (hcl5_khead KE, KE, Tsh, l_it L, T).
  { apply (hcl5_p5_ksnap_pre PS KE T HT Hptr). }
  change (ptable Tsh (l_pt L) head) with (ptable Tsh (d_ptab (hcl5_D x25519 R L)) head).
  forward_call (Tsh, l_ds L, Tsh, l_w L, hcl5_D x25519 R L, Tsh, head).
  { pose proof (hcl5_p5_head head PS Hch Hptr).
    unfold hcl5_D, setup_dev; cbn.
    repeat constructor; try discriminate; auto; intro X; rewrite X in *; contradiction. }
  forward_call (gv, Tsh, l_ss L, S, w).
  assert (Hlen: Zlength NS = Zlength PS)
    by (rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS); f_equal; exact Hnp).
  assert (HpI: hn_p (Znth i NS) = peer_addr4 (Znth i PS))
    by (rewrite <- (Znth_map i hn_p NS), <- (Znth_map i peer_addr4 PS) by lia; f_equal; exact Hnp).
  destruct (hcl5_p5_snapped_in T NS PS i Hlen H2) as (N & HN & HNa & HNp).
  pose proof (hcl5_p5_node_acc (hcl5_head NS) (hnodes_snapped4 T NS PS) N HN) as A1.
  unfold hcl5_p5_acc in A1. sep_apply A1. clear A1. rewrite HNa, HNp. Intros.
  assert (HinP: In (Znth i PS) PS) by (apply Znth_In; lia).
  assert (Hpp: isptr (hn_p (Znth i NS))) by (rewrite HpI; rewrite Forall_forall in Hptr; exact (Hptr _ HinP)).
  forward.
  forward.
  match goal with |- context [temp HCL5._h ?v] =>
    replace v with (hs_addr (hn_p (Znth i NS))) by (unfold hs_addr, OFS_PEER_HANDSHAKE; f_equal; vm_compute; reflexivity) end.
  sep_apply (hcl5_p5_mp (@field_at W Ews t_hnode4 (DOT HC._p) (hn_p (Znth i NS)) (hn_addr (Znth i NS)))
    (hnodes_rep4 W (hcl5_head NS) (hnodes_snapped4 T NS PS))).
  rewrite (hcl5_p5_split PS i) by lia.
  rewrite HpI.
  destruct (Znth i PS) as [[p sh] P] eqn:EP. cbn [peer_item_rep peer_addr4] in *.
  assert (HP: hcl5_pok L (p, sh, P)) by (rewrite Forall_forall in Hpok; apply Hpok; exact HinP).
  destruct HP as (-> & Hdev & _).
  pose proof (hcl5_p5_inpool PS KE T (p, Ews, P) HT HinP) as Hpool. cbn in Hpool.
  change (itable Tsh (l_it L) T) with (itable Tsh (d_itab (hcl5_D x25519 R L)) T).
  Intros.
  forward_call (Ews, p, P, Tsh, l_w L, hcl5_D x25519 R L, Tsh, T).
  unfold hcl5_S5. Exists R S w NS PS T head KE i.
  unfold hcl5_lvars, hcl5_scr, hcl5_world, hcl5_globs; cbn [app].
  unfold hcl5_clr. rewrite EP. cbn [hcl5_clr1]. rewrite (hcl5_p5_split_upd PS i) by lia.
  rewrite HpI.
  change (d_itab (hcl5_D x25519 R L)) with (l_it L).
  change (d_ptab (hcl5_D x25519 R L)) with (l_pt L).
  cbn [peer_item_rep].
  entailer!.
Qed.

End P5.
