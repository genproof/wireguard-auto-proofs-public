(* law consume_initiation_any, phase P7: separation-logic access to the fields main's model
   block passes or loads (byte buffers of the message, of ci, of a peer's remote static, of a node's snapshot; a
   node of the list as ONE value typed at the world W; valid pointers of the nodes).  Port of v1's hci3_p7_sep.v,
   hci3_p7_acc.v, hci3_p7_nv.v to hnodes_rep4 (struct hnode with `rest`, node at CKS).

   Offsets (x86_64): message: ephemeral 8, encrypted_static 40, encrypted_timestamp 88; m_consumed_initiation:
   spub 96, ts 128; wg_peer: handshake 48, its remote_static 88 (136 from the peer); hnode: snap 8, its
   latest_timestamp 272 (280 from the node). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require WgNoise.harness.x_consume_initiation_any.code.
Local Open Scope logic.

Module HCI := WgNoise.harness.x_consume_initiation_any.code.

#[export] Instance hci5_p7_cceH : change_composite_env HCS W_consume_initiation_any.
Proof. make_cs_preserve HCS W_consume_initiation_any. Defined.
#[export] Instance hci5_p7_cceK : change_composite_env CKS W_consume_initiation_any.
Proof. make_cs_preserve CKS W_consume_initiation_any. Defined.

(* ---- helpers ---- *)
#[local] Instance hci5_p7_sep_cce_NH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

Lemma hci5_p7_sep_NH sh n (v: list val) p :
  @data_at Noise.CS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

(* access: P gives Q and takes it back *)
Definition hci5_p7_sep_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hci5_p7_sep_acc_refl Q : hci5_p7_sep_acc Q Q.
Proof.
  unfold hci5_p7_sep_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hci5_p7_sep_acc_eq Q A : Q = A -> hci5_p7_sep_acc Q A.
Proof. intros ->. apply hci5_p7_sep_acc_refl. Qed.

Lemma hci5_p7_sep_acc_l Q A F : hci5_p7_sep_acc Q A -> hci5_p7_sep_acc Q (A * F).
Proof.
  unfold hci5_p7_sep_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hci5_p7_sep_acc_r Q A F : hci5_p7_sep_acc Q A -> hci5_p7_sep_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hci5_p7_sep_acc_l, H. Qed.

Lemma hci5_p7_sep_acc_prop Q (c: Prop) A : (c -> hci5_p7_sep_acc Q A) -> hci5_p7_sep_acc Q (!! c && A).
Proof.
  unfold hci5_p7_sep_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hci5_p7_sep_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hci5_p7_sep_acc Q (A x)) -> hci5_p7_sep_acc Q (EX x, A x).
Proof.
  unfold hci5_p7_sep_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

Lemma hci5_p7_sep_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hci5_p7_sep_acc Q A) -> hci5_p7_sep_acc Q A.
Proof.
  unfold hci5_p7_sep_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hci5_p7_sep_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hci5_p7_sep_acc Q (f x) -> hci5_p7_sep_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hci5_p7_sep_acc_l, H | apply hci5_p7_sep_acc_r, IH, Hin].
Qed.

(* ---- the message, a peer's remote static (Noise.CS) ---- *)
Section N.
#[local] Existing Instance Noise.CS.

Lemma hci5_p7_msg_es sh m M : init_rep sh m M |--
     hbytes sh (im_eph M) (offset_val 8 m) * hbytes sh (im_encs M) (offset_val 40 m) *
     (hbytes sh (im_eph M) (offset_val 8 m) * hbytes sh (im_encs M) (offset_val 40 m) -* init_rep sh m M).
Proof.
  unfold init_rep. Intros. destruct H as (L1 & L2 & L3 & L4 & L5).
  assert_PROP (field_compatible t_init [] m) by entailer!. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_init [StructField I._unencrypted_ephemeral]),
          (field_at_data_at sh t_init [StructField I._encrypted_static]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes.
  rewrite L1, L2, <- !hci5_p7_sep_NH. cancel.
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right; repeat split; auto | cancel].
Qed.

Lemma hci5_p7_msg_t sh m M : init_rep sh m M |--
     hbytes sh (im_enct M) (offset_val 88 m) * (hbytes sh (im_enct M) (offset_val 88 m) -* init_rep sh m M).
Proof.
  unfold init_rep. Intros. destruct H as (L1 & L2 & L3 & L4 & L5).
  assert_PROP (field_compatible t_init [] m) by entailer!. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_init [StructField I._encrypted_timestamp]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes.
  rewrite L3, <- !hci5_p7_sep_NH. cancel.
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right; repeat split; auto | cancel].
Qed.

Lemma hci5_p7_sep_rstatic sh a H : Zlength (hs_rstatic H) = 32 ->
  hci5_p7_sep_acc (hbytes sh (hs_rstatic H) (offset_val 136 a))
    (field_at sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) (hs_addr a)).
Proof.
  intros L. apply hci5_p7_sep_acc_pure with (c := field_compatible t_hs [StructField I._remote_static] (hs_addr a));
    [entailer! | intros FC].
  apply hci5_p7_sep_acc_eq. rewrite field_at_data_at, field_address_offset by auto.
  unfold hbytes, hs_addr. rewrite L, offset_offset_val, <- hci5_p7_sep_NH. reflexivity.
Qed.

Lemma hci5_p7_sep_c5 a sh P :
  hci5_p7_sep_acc (hbytes sh (hs_rstatic (p_hs P)) (offset_val 136 a)) (peer_rep sh a P).
Proof.
  unfold peer_rep. apply hci5_p7_sep_acc_prop; intros _.
  do 7 apply hci5_p7_sep_acc_l. apply hci5_p7_sep_acc_r.
  unfold hs_rep. apply hci5_p7_sep_acc_prop; intros (L1 & L2 & _).
  do 10 apply hci5_p7_sep_acc_l. apply hci5_p7_sep_acc_r. apply hci5_p7_sep_rstatic, L2.
Qed.

End N.

Lemma hci5_p7_peer_rs PS a sh P : In (a, sh, P) PS ->
  peers_rep PS |--
  hbytes sh (hs_rstatic (p_hs P)) (offset_val 136 a) *
  (hbytes sh (hs_rstatic (p_hs P)) (offset_val 136 a) -* peers_rep PS).
Proof.
  intros Hin. unfold peers_rep.
  apply (hci5_p7_sep_acc_iter _ _ (a, sh, P)); [exact Hin |]. apply hci5_p7_sep_c5.
Qed.

(* ---- ci (HCS) ---- *)
Section H.
#[local] Existing Instance HCS.

Lemma hci5_p7_ci_spub sh ck h key s tsv ci : Zlength s = 32 ->
     data_at sh t_mcinit (mcinit_val ck h key (bytes s) tsv) ci |--
     hbytes sh s (offset_val 96 ci) *
     (hbytes sh s (offset_val 96 ci) -* data_at sh t_mcinit (mcinit_val ck h key (bytes s) tsv) ci).
Proof.
  intros L. assert_PROP (field_compatible t_mcinit [] ci) by entailer!.
  unfold mcinit_val. unfold_data_at (data_at _ _ _ ci).
  rewrite (field_at_data_at sh t_mcinit [StructField HH._spub]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes. rewrite L. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

Lemma hci5_p7_ci_ts sh ck h key spub t ci : Zlength t = 12 ->
     data_at sh t_mcinit (mcinit_val ck h key spub (bytes t)) ci |--
     hbytes sh t (offset_val 128 ci) *
     (hbytes sh t (offset_val 128 ci) -* data_at sh t_mcinit (mcinit_val ck h key spub (bytes t)) ci).
Proof.
  intros L. assert_PROP (field_compatible t_mcinit [] ci) by entailer!.
  unfold mcinit_val. unfold_data_at (data_at _ _ _ ci).
  rewrite (field_at_data_at sh t_mcinit [StructField HH._ts]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes. rewrite L. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

Lemma hci5_p7_sep_snap_ts sh sn y : Zlength (hs_ts (sn_hs sn)) = 12 ->
  hci5_p7_sep_acc (hbytes sh (hs_ts (sn_hs sn)) (offset_val 272 y)) (data_at sh t_hsnap (hsnap_val sn) y).
Proof.
  intros L. unfold hci5_p7_sep_acc. assert_PROP (field_compatible t_hsnap [] y) by entailer!.
  unfold hsnap_val. unfold_data_at (data_at _ _ _ y).
  rewrite (field_at_data_at sh t_hsnap [StructField HH._latest_timestamp]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes. rewrite L. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

End H.

Lemma hci5_p7_mident_cs sh I p : @data_at HCS sh t_mident (mident_val I) p =
  @data_at W_consume_initiation_any sh t_mident
    (bytes (mi_priv I), (bytes (mi_pub I), Vint (if mi_ok I then Int.one else Int.zero))) p.
Proof. set (v := mident_val I). rewrite (@data_at_change_composite HCS W_consume_initiation_any _ sh t_mident v v (JMeq_refl _)); [reflexivity | prove_cs_preserve_type]. Qed.

(* ---- the nodes ---- *)
Lemma hci5_p7_sep_KW sh (v: @reptype CKS t_hnode4) x :
  @data_at CKS sh t_hnode4 v x = @data_at W_consume_initiation_any sh t_hnode4 v x.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hci5_p7_sep_HW sh (v: @reptype HCS t_hsnap) y :
  @data_at HCS sh t_hsnap v y = @data_at W_consume_initiation_any sh t_hsnap v y.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hci5_p7_sep_head l NS : hnodes_rep4 W l NS |-- !! (l = hci5_head NS).
Proof. destruct NS as [|N NS]; simpl; entailer!. Qed.

Lemma hci5_p7_sep_c6 NS1 N NS2 l :
  hci5_p7_sep_acc (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hci5_head NS2)))) (hn_addr N))
    (hnodes_rep4 W l (NS1 ++ N :: NS2)).
Proof.
  revert l; induction NS1 as [|M NS1 IH]; intros l; simpl.
  - apply hci5_p7_sep_acc_prop; intros ->. apply hci5_p7_sep_acc_ex; intros nx.
    apply hci5_p7_sep_acc_pure with (c := nx = hci5_head NS2).
    { sep_apply (hci5_p7_sep_head nx NS2). entailer!. }
    intros ->. do 2 apply hci5_p7_sep_acc_l. apply hci5_p7_sep_acc_r, hci5_p7_sep_acc_refl.
  - apply hci5_p7_sep_acc_prop; intros _. apply hci5_p7_sep_acc_ex; intros nx.
    apply hci5_p7_sep_acc_r, IH.
Qed.

Lemma hci5_p7_hn_valid l NS a : In a (map hn_addr NS) -> hnodes_rep4 W l NS |-- valid_pointer a.
Proof.
  revert l; induction NS as [|N NS IH]; intros l Hin; simpl in *; [contradiction|].
  Intros nx. destruct Hin as [<-|Hin].
  - subst l. auto with valid_pointer.
  - apply sepcon_valid_pointer2, IH, Hin.
Qed.

Lemma hci5_p7_hn_isptr l NS : hnodes_rep4 W l NS |-- !! Forall isptr (map hn_addr NS).
Proof.
  revert l; induction NS as [|N NS IH]; intros l; simpl; [entailer!|].
  Intros nx. sep_apply (IH nx). entailer!.
Qed.

(* a node's value as ONE constant at W *)
Definition hci5_p7_nv (N: hnode4) (nx: val) : @reptype W_consume_initiation_any t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hci5_p7_nv_node NS1 N NS2 :
  hnodes_rep4 W (hci5_head (NS1 ++ N :: NS2)) (NS1 ++ N :: NS2) |--
  @data_at W_consume_initiation_any Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N) *
  (@data_at W_consume_initiation_any Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N) -*
   hnodes_rep4 W (hci5_head (NS1 ++ N :: NS2)) (NS1 ++ N :: NS2)).
Proof.
  unfold hci5_p7_nv. rewrite <- hci5_p7_sep_KW. apply hci5_p7_sep_c6.
Qed.

(* the node's value with its snapshot exposed *)
Definition hci5_p7_nvs (N: hnode4) (sn: hsnap) (nx: val) : @reptype W_consume_initiation_any t_hnode4 :=
  (hn_p N, (hsnap_val sn, (hn_refs N, (hn_rest N, nx)))).

Lemma hci5_p7_nv_nvs sh N nx x sn : hn_snap N = hsnap_val sn ->
  @data_at W_consume_initiation_any sh t_hnode4 (hci5_p7_nv N nx) x =
  @data_at W_consume_initiation_any sh t_hnode4 (hci5_p7_nvs N sn nx) x.
Proof. intros Hs. unfold hci5_p7_nv, hci5_p7_nvs. rewrite Hs. reflexivity. Qed.

Section Wsec.
#[local] Existing Instance W_consume_initiation_any.

Lemma hci5_p7_sep_c7 sh (pp: val) sn (r rest nx x: val) (rs: @reptype W_consume_initiation_any t_prsnap) :
  Zlength (hs_ts (sn_hs sn)) = 12 ->
  hci5_p7_sep_acc (hbytes sh (hs_ts (sn_hs sn)) (offset_val 280 x))
    (data_at sh t_hnode4 (pp, (hsnap_val sn, (r, (rs, nx)))) x).
Proof.
  intros L. apply hci5_p7_sep_acc_pure with (c := field_compatible t_hnode4 [] x); [entailer! | intros FC].
  unfold_data_at (data_at _ _ _ x).
  apply hci5_p7_sep_acc_r, hci5_p7_sep_acc_l.
  rewrite (field_at_data_at sh t_hnode4 [StructField HCI._snap]), field_address_offset by auto with field_compatible.
  change (nested_field_type t_hnode4 [StructField HCI._snap]) with t_hsnap.
  rewrite <- hci5_p7_sep_HW. simpl (offset_val _ _).
  replace (offset_val 280 x) with (offset_val 272 (offset_val 8 x)) by (rewrite offset_offset_val; reflexivity).
  apply hci5_p7_sep_snap_ts, L.
Qed.

End Wsec.

Lemma hci5_p7_nv_ts sh N nx x sn : hn_snap N = hsnap_val sn -> Zlength (hs_ts (sn_hs sn)) = 12 ->
  @data_at W_consume_initiation_any sh t_hnode4 (hci5_p7_nv N nx) x |--
  hbytes sh (hs_ts (sn_hs sn)) (offset_val 280 x) *
  (hbytes sh (hs_ts (sn_hs sn)) (offset_val 280 x) -* @data_at W_consume_initiation_any sh t_hnode4 (hci5_p7_nv N nx) x).
Proof. intros Hs Hl. unfold hci5_p7_nv. rewrite Hs. apply (hci5_p7_sep_c7 sh _ sn _ Vundef). exact Hl. Qed.

(* ---- misc ---- *)
Lemma hci5_p7_init_isptr sh m M : init_rep sh m M |-- !! isptr m.
Proof. unfold init_rep. Intros. entailer!. Qed.
#[export] Hint Resolve hci5_p7_init_isptr : saturate_local.

Lemma hci5_p7_hn_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [|N NS]; simpl.
  - entailer!.
  - Intros nx. entailer!.
Qed.
#[export] Hint Resolve hci5_p7_hn_pn : saturate_local.

Lemma hci5_p7_peers_hsok PS a sh P : In (a, sh, P) PS -> peers_rep PS |-- !! (hs_ok (p_hs P) /\ isptr a).
Proof.
  intros Hin. apply in_split in Hin. destruct Hin as (l1 & l2 & ->).
  unfold peers_rep. rewrite iter_sepcon_app. simpl. unfold peer_rep, hs_rep. entailer!.
  all: try (match goal with Hf: field_compatible t_peer [] _ |- _ => destruct Hf; auto end).
Qed.

Lemma hci5_p7_head_pn NS1 N NS2 :
  Forall isptr (map hn_addr (NS1 ++ N :: NS2)) -> is_pointer_or_null (hci5_head NS2).
Proof.
  intros Hf. rewrite map_app, Forall_app in Hf. destruct Hf as [_ Hf]. inversion Hf; subst.
  destruct NS2 as [|N2 NS2]; simpl; auto. inversion H2; subst. destruct (hn_addr N2); try contradiction; exact I.
Qed.

Lemma hci5_p7_split_T bs p : hbytes Tsh bs p |-- hbytes Ews bs p * hbytes (Share.comp Ews) bs p.
Proof. unfold hbytes. rewrite (data_at_share_join Ews (Share.comp Ews) Tsh); [apply derives_refl | apply join_comp_Tsh]. Qed.
Lemma hci5_p7_join_T bs p : hbytes Ews bs p * hbytes (Share.comp Ews) bs p |-- hbytes Tsh bs p.
Proof. unfold hbytes. rewrite (data_at_share_join Ews (Share.comp Ews) Tsh); [apply derives_refl | apply join_comp_Tsh]. Qed.

Lemma hci5_p7_head_snapped T NS PS : hnodes_peers4 NS PS -> hci5_head (hnodes_snapped4 T NS PS) = hci5_head NS.
Proof.
  unfold hnodes_peers4, hnodes_snapped4. destruct NS as [|N NS], PS as [|x PS]; simpl; intros Hm;
    try discriminate; auto.
  destruct x as [[p sh] P]. reflexivity.
Qed.

Lemma hci5_p7_hout bs p : Zlength bs = 32 -> hbytes Tsh bs p |-- hout Tsh 32 p.
Proof. intros Hl. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hci5_p7_wand1 (A Q: mpred) : A * (A -* Q) |-- Q.
Proof. apply wand_frame_elim. Qed.
Lemma hci5_p7_wand2 (A B Q: mpred) : A * B * (A * B -* Q) |-- Q.
Proof. apply wand_frame_elim. Qed.

Ltac hci5_p7_absurd := exfalso; first
  [ match goal with H: ?x <> ?x |- _ => apply H; reflexivity end
  | match goal with H: Int.one = Int.zero |- _ => discriminate H end
  | match goal with H: Int.zero = Int.one |- _ => discriminate H end
  | match goal with H: false = true |- _ => discriminate H end
  | match goal with H: true = false |- _ => discriminate H end ].
