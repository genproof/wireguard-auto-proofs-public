(*
   - the message object as bytes (dispatch takes bytes_at at skb->data): the cookie message's image (the analogue of
     prot_rep3_init_eq / resp_eq), obj_rep = token * bytes_at;
   - D's device split into its checker's secret / birthdate and the rest (port of hrx5_PA_lem.v's hrx5_pa_ lemmas);
   - the index table's head at the world's compspecs;
   - rxw_ok of the world before dispatch from the loop's invariant. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Local Open Scope logic.

#[local] Instance hrx5_b5_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_b5_cce_C : change_composite_env Cookie.CS W.
Proof. make_cs_preserve Cookie.CS W. Defined.

(* ---------------------------------------------------------------------- *)
(* the cookie message's image                                              *)
(* ---------------------------------------------------------------------- *)

Section CK.
#[local] Existing Instance Cookie.CS.

Lemma hrx5_b5_cmsg_eq sh m M :
  field_compatible t_cmsg [] m -> cm_ok M ->
  data_at sh t_cmsg (cmsg_val M) m = bytes_at sh (cookie_msg_bytes M) m.
Proof.
  intros FC OK.
  unfold_data_at (data_at sh t_cmsg (cmsg_val M) m).
  assert (EH: forall v, field_at sh t_cmsg (DOT cookie.code._header) v m =
                        field_at sh t_cmsg (DOT cookie.code._header DOT cookie.code._type) v m).
  { intros v. apply pred_ext. unfold_field_at 1%nat. cancel. unfold_field_at 2%nat. cancel. }
  rewrite EH; clear EH.
  rewrite !field_at_data_at.
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset. unfold cmsg_val; simpl fst; simpl snd.
  rewrite (prot_rep3_u32_le sh (cm_type M) (offset_val 0 m))
    by exact (field_compatible_nested_field t_cmsg (DOT cookie.code._header DOT cookie.code._type) m
                ltac:(auto with field_compatible)).
  rewrite (prot_rep3_u32_le sh (cm_receiver M) (offset_val 4 m))
    by exact (field_compatible_nested_field t_cmsg (DOT cookie.code._receiver_index) m
                ltac:(auto with field_compatible)).
  rewrite !(@data_at_tarray_tuchar_cs Cookie.CS Noise.CS).
  destruct OK as (L1 & L2).
  assert (FB: forall k len, 0 <= k -> 0 <= len -> k + len <= 64 ->
            @field_compatible Noise.CS (tarray tuchar len) [] (offset_val k m)).
  { intros k len Hk Hl Hn. apply (@field_compatible_tarray_tuchar_cs Cookie.CS Noise.CS).
    apply (prot_rep3_fc_bytes t_cmsg); auto. }
  replace (bytes_at sh (cookie_msg_bytes M) m) with (bytes_at sh (cookie_msg_bytes M) (offset_val 0 m))
    by (rewrite isptr_offset_val_zero by (destruct FC; auto); reflexivity).
  unfold cookie_msg_bytes.
  rewrite (prot_rep3_bytes_app_at sh (le32 (cm_type M)) _ m 0 4 4 60)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia; apply FB; lia).
  rewrite (prot_rep3_bytes_app_at sh (le32 (cm_receiver M)) _ m 4 8 4 56)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia; apply FB; lia).
  rewrite (prot_rep3_bytes_app_at sh (cm_nonce M) _ m 8 32 24 32)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia; apply FB; lia).
  unfold bytes_at. rewrite !prot_rep3_le32_len, L1, L2. reflexivity.
Qed.

End CK.

(* ---------------------------------------------------------------------- *)
(* the message object = its malloc token * its bytes                      *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_b5_tok (dp: val) (o: hrx5_obj) : mpred :=
  match o with
  | OBuf b => @malloc_token W Ews (tarray tuchar (Zlength b)) dp
  | OInit _ => @malloc_token W Ews t_init dp
  | OResp _ => @malloc_token W Ews t_resp dp
  | OCookie _ => @malloc_token W Ews t_cmsg dp
  end.

Lemma hrx5_b5_obj_len o : obj_ok o -> 0 <= Zlength (obj_bytes o) <= Int.max_unsigned.
Proof.
  destruct o as [b|M|M|M]; simpl; intros OK.
  - pose proof (Zlength_nonneg b). lia.
  - destruct OK as (L1&L2&L3&L4&L5). unfold init_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4, L5. rep_lia.
  - destruct OK as (L1&L2&L3&L4). unfold resp_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4. rep_lia.
  - destruct OK as (L1&L2). unfold cookie_msg_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2. rep_lia.
Qed.

Lemma hrx5_b5_obj_open dp o : obj_ok o -> malloc_compatible (Zlength (obj_bytes o)) dp ->
  obj_rep dp o = hrx5_b5_tok dp o * bytes_at Ews (obj_bytes o) dp.
Proof.
  intros OK MC. destruct o as [b|M|M|M]; simpl in MC |- *; [reflexivity | | |].
  - unfold init_rep. rewrite prop_true_andp by exact OK.
    rewrite prot_rep3_init_eq; [reflexivity | | exact OK].
    apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
    replace (sizeof t_init) with (Zlength (init_bytes M)); [exact MC |].
    destruct OK as (L1&L2&L3&L4&L5). unfold init_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4, L5. reflexivity.
  - unfold resp_rep. rewrite prop_true_andp by exact OK.
    rewrite prot_rep3_resp_eq; [reflexivity | | exact OK].
    apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
    replace (sizeof t_resp) with (Zlength (resp_bytes M)); [exact MC |].
    destruct OK as (L1&L2&L3&L4). unfold resp_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4. reflexivity.
  - unfold cmsg_rep. rewrite prop_true_andp by exact OK.
    rewrite hrx5_b5_cmsg_eq; [reflexivity | | exact OK].
    apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
    replace (@sizeof Cookie.CS t_cmsg) with (Zlength (cookie_msg_bytes M)); [exact MC |].
    destruct OK as (L1&L2). unfold cookie_msg_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* D's device: the checker's secret and birthdate (hrx5_PA_lem.v's)       *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_b5_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Definition hrx5_b5_drest (sh: share) (wg: val) (D: device) : mpred :=
  !! @field_compatible Noise.CS t_dev [] wg &&
  (@field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg *
   identity_rep sh (id_addr wg) (d_id D) *
   @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   @field_at Noise.CS sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

Lemma hrx5_b5_dev_split sh wg D :
  device_rep sh wg D = hrx5_b5_drest sh wg D * checker_rep sh (cc_addr wg) (d_cc D).
Proof.
  unfold device_rep, hrx5_b5_drest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

Lemma hrx5_b5_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Lemma hrx5_b5_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) v wg =
  field_at sh t_cc (DOT I._secret_birthdate) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W hrx5_b5_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hrx5_b5_fc_cc; exact FC).
  rewrite (@field_at_data_at W). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hrx5_b5_tulong_cs.
Qed.

Definition hrx5_b5_ccrest (sh: share) (a: val) (CC: checker) : mpred :=
  EX lk: val, field_at sh t_cc (DOT I._cookie_encryption_key) (bytes (cc_ekey CC)) a *
              field_at sh t_cc (DOT I._message_mac1_key) (bytes (cc_mkey CC)) a *
              field_at sh t_cc (DOT I._secret_lock) lk a *
              field_at sh t_cc (DOT I._device) (cc_dev CC) a * spacer sh 108 112 a.

Lemma hrx5_b5_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC =
  !! cc_ok CC &&
  (hbytes sh (cc_secret CC) (cc_addr wg) *
   @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
   hrx5_b5_ccrest sh (cc_addr wg) CC).
Proof.
  intros FC. pose proof (hrx5_b5_fc_cc _ FC) as FCc.
  unfold checker_rep, hrx5_b5_ccrest. rewrite hrx5_b5_cc_birth by exact FC.
  forget (cc_addr wg) as a.
  apply pred_ext.
  - Intros lk. pose proof H as (L1 & L2 & L3).
    unfold hbytes. rewrite L1. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cc _ a).
    rewrite (field_at_data_at sh t_cc (DOT I._secret)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    Exists lk. entailer!.
  - Intros lk. Exists lk. pose proof H as (L1 & L2 & L3).
    unfold hbytes. rewrite L1. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cc _ a).
    rewrite (field_at_data_at sh t_cc (DOT I._secret)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    entailer!.
Qed.

Lemma hrx5_b5_cc_close sh wg CC : field_compatible t_dev [] wg -> cc_ok CC ->
  hbytes sh (cc_secret CC) (cc_addr wg) *
  @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
  hrx5_b5_ccrest sh (cc_addr wg) CC |-- checker_rep sh (cc_addr wg) CC.
Proof.
  intros FC H. rewrite hrx5_b5_cc_open by exact FC.
  apply andp_right; [apply prop_right; exact H | apply derives_refl].
Qed.

End Fields.

(* the index table's head at the world's compspecs *)
Lemma hrx5_b5_itab_cs sh v p : @data_at Noise.CS sh t_itab v p = @data_at W sh t_itab v p.
Proof.
  exact (equal_f (@data_at_change_composite Noise.CS W hrx5_b5_cce_N sh t_itab v v (JMeq_refl v) ltac:(reflexivity)) p).
Qed.

(* ---------------------------------------------------------------------- *)
(* pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_b5_head_def head PS : pk_chain head PS -> peers_rep PS |-- !! (head <> Vundef).
Proof.
  destruct PS as [| [[a sh] P] PS]; simpl; intros Hc.
  - subst. apply prop_right. discriminate.
  - destruct Hc as [-> _]. unfold peers_rep. simpl iter_sepcon. unfold peer_item_rep, peer_rep.
    Intros. apply prop_right. intro E; subst. destruct H as (Hp & _); exact Hp.
Qed.

Lemma hrx5_b5_f2l {A B: Type} (P: A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> Forall (fun x => exists y, In y l2 /\ P x y) l1.
Proof.
  induction 1; constructor.
  - exists y. split; [left; reflexivity | assumption].
  - eapply Forall_impl; [| exact IHForall2]. intros a (b & Hb & Hp). exists b. split; [right |]; assumption.
Qed.

Lemma hrx5_b5_f2r {A B: Type} (P: A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> Forall (fun y => exists x, In x l1 /\ P x y) l2.
Proof.
  induction 1; constructor.
  - exists x. split; [left; reflexivity | assumption].
  - eapply Forall_impl; [| exact IHForall2]. intros b (a & Ha & Hp). exists a. split; [right |]; assumption.
Qed.

Lemma hrx5_b5_sfind_nodup {A: Type} (D: list (val * share * A)) a sh E :
  NoDup (saddrs D) -> In (a, sh, E) D -> sfind D a = Some (sh, E).
Proof.
  induction D as [| [[x shx] Ex] D IH]; simpl; [tauto |]. intros Hnd Hin.
  inversion Hnd as [| ? ? Hni Hnd']; subst.
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct Hin as [Heq | Hin]; [congruence |].
    exfalso. apply Hni. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto.
  - destruct Hin as [Heq | Hin]; [congruence | auto].
Qed.

Lemma hrx5_b5_sfind (PS: list (val * share * peer)) a sh P :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS -> sfind PS a = Some (sh, P).
Proof.
  induction PS as [| [[b sh'] P'] PS IH]; intros Hnd Hin; [destruct Hin |].
  cbn [map peer_addr4] in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst. cbn [sfind].
  destruct Hin as [Heq | Hin].
  - inversion Heq; subst. rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false; [auto |]. intro Hba; subst b. apply Hnin.
    change a with (peer_addr4 (a, sh, P)). apply in_map. exact Hin.
Qed.

Lemma hrx5_b5_paddr x : hrx5cr_paddr x = peer_addr4 x.
Proof. destruct x as [[a sh] P]; reflexivity. Qed.

(* the receive world before dispatch *)
Lemma hrx5_b5_rxw_fold gv wg head D T PS S w kc lul :
  device_rep Tsh wg D * itable Tsh (d_itab D) T * ptable Tsh (d_ptab D) head * peers_rep PS *
  shim_state4 gv S w * noise_globals gv kc * lul_rep gv lul * rxlog_rep gv rx0
  |-- rxw_rep W gv Tsh wg head (hrx5_W0 D T PS S w kc lul).
Proof.
  unfold rxw_rep, hrx5_W0; cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  unfold keypairs_rep; simpl iter_sepcon. cancel.
Qed.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.

Lemma hrx5_b5_rxw_ok R L NS PS KE T head nk D S w kc lul :
  hrx5_inv x25519 R L NS PS KE T head nk -> itable_wf T ->
  rxw_ok (l_wd L) head (hrx5_W0 D T PS S w kc lul).
Proof.
  intros (Hpok & Hwf & Hnd & Hch & _ & _ & Hke & Hhs) (_ & _ & HndT & _).
  unfold rxw_ok, hrx5_W0; cbn [rw_PS rw_T rw_KS rw_rx]. split; [exact Hch |]. split; [| split; reflexivity].
  assert (Hrefs: Forall (fun x => match x with (_, _, P) => p_refs P <> Int.zero end) PS).
  { eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] (_ & _ & _ & _ & _ & Hr & _).
    intro Hc. rewrite Hc, Int.unsigned_zero in Hr. lia. }
  rewrite Forall_forall in Hrefs.
  unfold rx_peers_ok. split; [exact Hwf |]. split; [| split].
  - unfold peers_refs_ok. eapply Forall_impl; [| exact Hpok].
    intros [[a sh] P] (_ & _ & _ & _ & _ & Hr & _). exact Hr.
  - unfold pool_peers_ok. rewrite <- (firstn_skipn (length (map ke_addr KE)) (t_D T)). apply Forall_app. split.
    + apply hrx5_b5_f2r in Hke. eapply Forall_impl; [| exact Hke].
      intros [[a sh] E] (k & _ & Ha & Hsh & Hp & Ht).
      split; [| right; exact Ht].
      apply in_map_iff in Hp. destruct Hp as ([[p shp] P] & Hp & HP). cbn in Hp. rewrite <- Hp.
      exists shp, P. split; [apply hrx5_b5_sfind; assumption |].
      exact (Hrefs _ HP).
    + apply hrx5_b5_f2r in Hhs. eapply Forall_impl; [| exact Hhs].
      intros [[a sh] E] ([[p shp] P] & HP & Ha & Hsh & Hp & Ht).
      split; [| left; split; [exact Ht | rewrite Hp; exact Ha]].
      exists shp, P. rewrite Hp. split; [apply hrx5_b5_sfind; assumption |].
      exact (Hrefs _ HP).
  - apply hrx5_b5_f2l in Hhs. rewrite Forall_forall in Hhs, Hpok |- *.
    intros [[p sh] P] HP. specialize (Hpok _ HP). specialize (Hhs _ HP).
    destruct Hpok as (_ & Hdev & _ & _ & _ & _ & Hlic & _ & Hc & Hpv & Hn).
    destruct Hhs as ([[a she] E] & HE & Ha & Hsh & Hp & _).
    split; [exact Hdev |]. split; [exact Hc |]. split; [exact Hpv |]. split; [exact Hn |]. split.
    + exists E. split; [| exact Hp]. unfold t_entry. subst a.
      rewrite (hrx5_b5_sfind_nodup (t_D T) (hs_addr p) she E HndT); [reflexivity |].
      rewrite <- (firstn_skipn (length (map ke_addr KE)) (t_D T)). apply in_app_iff. right. exact HE.
    + rewrite Int64.signed_eq_unsigned by (unfold Int64.max_signed, Int64.half_modulus, Int64.modulus,
        Int64.wordsize, Wordsize_64.wordsize in *; simpl in *; lia).
      unfold Int64.max_signed, Int64.half_modulus, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize in *.
      simpl in *. lia.
Qed.

End Pure.

