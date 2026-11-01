(* body of hs_same_but_next (v4 spec), closes hc4_body_hs_same_but_next *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.

Module FH := WgNoise.harness.x_handshake.code.
Module FKP := WgNoise.harness.x_keypairs.code.

(* ---- the lent objects' addresses are valid pointers ---- *)
Section VP.
#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Lemma hc4nb2_hs_sbn_vp_peer0 sh p P R :
  readable_share sh -> peer_rep sh p P * R |-- valid_pointer p.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold peer_rep. Intros.
  do 10 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hc4nb2_hs_sbn_vp_peers PS x R :
  Forall (fun x => match x with (_, sh, _) => readable_share sh end) PS -> In x (map peer_addr4 PS) ->
  peers_rep PS * R |-- valid_pointer x.
Proof.
  revert R. induction PS as [|[[a sh] P] PS IH]; simpl; intros R HF Hin; [contradiction|].
  inversion HF; subst. unfold peers_rep in *. simpl iter_sepcon. destruct Hin as [<- | Hin].
  - rewrite sepcon_assoc. apply hc4nb2_hs_sbn_vp_peer0; auto.
  - rewrite sepcon_assoc, (sepcon_comm (peer_rep sh a P)), sepcon_assoc. apply IH; auto.
Qed.

Lemma hc4nb2_hs_sbn_vp_dev0 sh wg D x R :
  readable_share sh -> In x [wg; id_addr wg; cc_addr wg] -> device_rep sh wg D * R |-- valid_pointer x.
Proof.
  intros RS Hin. apply sepcon_valid_pointer1. unfold device_rep, identity_rep, checker_rep. Intros.
  destruct Hin as [<- | [<- | [<- | []]]].
  - do 4 apply sepcon_valid_pointer1.
    apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
  - Intros lk1 lk2. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl; lia].
  - Intros lk1 lk2. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4nb2_hs_sbn_saddrs_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct H as [<- | H]; [eauto|]. destruct (IH H) as (sh & E & HI). eauto.
Qed.

Lemma hc4nb2_hs_sbn_vp_itab sh tab T x R :
  readable_share sh -> In x (tab :: saddrs (t_D T)) -> itable sh tab T * R |-- valid_pointer x.
Proof.
  intros RS [<- | Hin].
  - apply sepcon_valid_pointer1. unfold itable. Intros. apply sepcon_valid_pointer1.
    apply data_at_valid_ptr; [auto | simpl; lia].
  - apply sepcon_valid_pointer1. unfold itable. Intros. apply sepcon_valid_pointer2.
    destruct (hc4nb2_hs_sbn_saddrs_in _ _ Hin) as (shx & E & HE).
    eapply derives_trans; [apply iter_sepcon_in_true; exact HE|].
    apply sepcon_valid_pointer1. unfold pool_item_rep, entry_at.
    assert (writable_share shx).
    { destruct H as (_ & _ & _ & HF). rewrite Forall_forall in HF. apply (HF _ HE). }
    apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

(* every lent address (v4.1: VKents / VKeypairs lend none; VTok an empty malloc'd object) *)
Lemma hc4nb2_hs_sbn_vp_obj CSw o x R :
  vobj_ok o -> In x (vobj_addrs o) -> vobj_rep CSw o * R |-- valid_pointer x.
Proof.
  destruct o; simpl; intros OK Hin; try contradiction.
  - destruct Hin as [<- | []]. apply hc4nb2_hs_sbn_vp_peer0; auto.
  - apply hc4nb2_hs_sbn_vp_peers; auto.
  - apply hc4nb2_hs_sbn_vp_dev0; auto.
  - apply hc4nb2_hs_sbn_vp_itab; auto.
  - destruct Hin as [<- | []]. destruct OK as [RS LEN]. apply sepcon_valid_pointer1.
    unfold bytes_at. apply data_at_valid_ptr; [auto | simpl; rewrite Z.max_r by lia; lia].
  - destruct Hin as [<- | []]. destruct OK as [RS LEN]. apply sepcon_valid_pointer1.
    apply memory_block_valid_ptr; [auto | lia].
  - destruct Hin as [<- | []]. apply sepcon_valid_pointer1.
    apply (@malloc_token_valid_pointer CSw). apply OK.
Qed.

Lemma hc4nb2_hs_sbn_vp_vobjs CSw VO x R :
  Forall vobj_ok VO -> In x (vobjs_addrs VO) -> vobjs CSw VO * R |-- valid_pointer x.
Proof.
  revert R. induction VO as [|o VO IH]; simpl; intros R HF Hin; [contradiction|].
  inversion HF; subst. unfold vobjs_addrs in Hin. simpl in Hin. apply in_app_or in Hin.
  unfold vobjs. simpl iter_sepcon. destruct Hin as [Hin | Hin].
  - rewrite sepcon_assoc. apply hc4nb2_hs_sbn_vp_obj; auto.
  - rewrite sepcon_assoc, (sepcon_comm (vobj_rep CSw o)), sepcon_assoc. apply IH; auto.
Qed.
End VP.

(* ---- helpers of hs_same_but_next (after v1's hc3_body_hs_same, hc3_body_snap.v) ---- *)
#[local] Existing Instance CSkhnb.
#[local] Instance hc4nb2_hs_sbn_i1 : change_composite_env HCS CSkhnb. make_cs_preserve HCS CSkhnb. Defined.
#[local] Instance hc4nb2_hs_sbn_i2 : change_composite_env CSkhnb HCS. make_cs_preserve CSkhnb HCS. Defined.
#[local] Instance hc4nb2_hs_sbn_i3 : change_composite_env Noise.CS CSkhnb. make_cs_preserve Noise.CS CSkhnb. Defined.
#[local] Instance hc4nb2_hs_sbn_i4 : change_composite_env CSkhnb Noise.CS. make_cs_preserve CSkhnb Noise.CS. Defined.

Lemma hc4nb2_hs_sbn_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  assert (forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (H (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (H (@cenv_cs cs2) (Ptrofs.unsigned i)). tauto.
Qed.

Local Open Scope logic.
Definition hc4nb2_hs_sbn_ths := Tstruct FH._noise_handshake noattr.

Lemma hc4nb2_hs_sbn_snap_eq shs (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
  @data_at HCS shs t_hsnap (a, (b, (c, (d, (e, (f, (g, (h, (l1, (l2, (l3, (l4, (l5, (l6, (l7, (l8, ri)))))))))))))))) s =
  field_at shs t_hsnap (DOT FH._peer) a s * field_at shs t_hsnap (DOT FH._next) b s *
  field_at shs t_hsnap (DOT FH._hashed) c s * spacer shs 17 20 s *
  field_at shs t_hsnap (DOT FH._type) d s * field_at shs t_hsnap (DOT FH._index) e s *
  field_at shs t_hsnap (DOT FH._state) f s * field_at shs t_hsnap (DOT FH._last_initiation_consumption) g s *
  field_at shs t_hsnap (DOT FH._static_identity) h s *
  data_at shs (tarray tuchar 32) l1 (field_address t_hsnap (DOT FH._ephemeral_private) s) *
  data_at shs (tarray tuchar 32) l2 (field_address t_hsnap (DOT FH._remote_static) s) *
  data_at shs (tarray tuchar 32) l3 (field_address t_hsnap (DOT FH._remote_ephemeral) s) *
  data_at shs (tarray tuchar 32) l4 (field_address t_hsnap (DOT FH._precomputed_static_static) s) *
  data_at shs (tarray tuchar 32) l5 (field_address t_hsnap (DOT FH._preshared_key) s) *
  data_at shs (tarray tuchar 32) l6 (field_address t_hsnap (DOT FH._hash) s) *
  data_at shs (tarray tuchar 32) l7 (field_address t_hsnap (DOT FH._chaining_key) s) *
  data_at shs (tarray tuchar 12) l8 (field_address t_hsnap (DOT FH._latest_timestamp) s) *
  field_at shs t_hsnap (DOT FH._remote_index) ri s.
Proof.
  rewrite (@data_at_change_composite HCS CSkhnb _ shs t_hsnap _ _ (JMeq_refl _)) by reflexivity.
  match goal with |- @data_at _ _ _ ?v _ = _ => set (V := v) end.
  unfold data_at. rewrite (@field_at_Tstruct CSkhnb shs t_hsnap [] FH._hs_snap noattr V V s eq_refl (JMeq_refl _)).
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at].
  simpl struct_pred. unfold withspacer. simpl nested_field_offset. simpl sizeof.
  repeat match goal with |- context [Z.eq_dec ?x ?y] =>
    destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
  subst V.
  rewrite (field_at_data_at shs t_hsnap (DOT FH._ephemeral_private)),
    (field_at_data_at shs t_hsnap (DOT FH._remote_static)),
    (field_at_data_at shs t_hsnap (DOT FH._remote_ephemeral)),
    (field_at_data_at shs t_hsnap (DOT FH._precomputed_static_static)),
    (field_at_data_at shs t_hsnap (DOT FH._preshared_key)),
    (field_at_data_at shs t_hsnap (DOT FH._hash)),
    (field_at_data_at shs t_hsnap (DOT FH._chaining_key)),
    (field_at_data_at shs t_hsnap (DOT FH._latest_timestamp)).
  simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

Lemma hc4nb2_hs_sbn_hbytes sh n A x :
  Zlength A = n -> @data_at CSkhnb sh (tarray tuchar n) (bytes A) x = hbytes sh A x.
Proof. intros <-. unfold hbytes. apply hc4nb2_hs_sbn_data_at_cs. Qed.

Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.

Lemma hc4nb2_hs_sbn_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hc4nb2_hs_sbn_sfind_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma hc4nb2_hs_sbn_sfind_In (D: list (val * share * entry)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Definition hc4nb2_hs_sbn_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk (hs_addr p)) *
   spacer sh 36 40 (hs_addr p) * spacer sh 300 304 (hs_addr p) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Definition hc4nb2_hs_sbn_hsf (sh: share) (h: val) (H: handshake) : mpred :=
  field_at sh t_hs (DOT FH._state) (Vint (hs_state H)) h *
  field_at sh t_hs (DOT FH._last_initiation_consumption) (Vlong (hs_lic H)) h *
  field_at sh t_hs (DOT FH._static_identity) (hs_sid H) h *
  hbytes sh (hs_eph H) (field_address t_hs (DOT FH._ephemeral_private) h) *
  hbytes sh (hs_rstatic H) (field_address t_hs (DOT FH._remote_static) h) *
  hbytes sh (hs_reph H) (field_address t_hs (DOT FH._remote_ephemeral) h) *
  hbytes sh (hs_ss H) (field_address t_hs (DOT FH._precomputed_static_static) h) *
  hbytes sh (hs_psk H) (field_address t_hs (DOT FH._preshared_key) h) *
  hbytes sh (hs_hash H) (field_address t_hs (DOT FH._hash) h) *
  hbytes sh (hs_ck H) (field_address t_hs (DOT FH._chaining_key) h) *
  hbytes sh (hs_ts H) (field_address t_hs (DOT FH._latest_timestamp) h) *
  field_at sh t_hs (DOT FH._remote_index) (Vint (hs_rindex H)) h.

Local Ltac hc4nb2_hs_sbn_cc f v :=
  rewrite (@field_at_change_composite Noise.CS CSkhnb _ _ t_hs (DOT f) v v (JMeq_refl v)) by reflexivity.

Lemma hc4nb2_hs_sbn_hsf_eq sh h H :
  hs_ok H ->
  hc4nb2_hs_sbn_hsf sh h H =
  @field_at Noise.CS sh t_hs [StructField I._state] (Vint (hs_state H)) h *
  @field_at Noise.CS sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
  @field_at Noise.CS sh t_hs [StructField I._static_identity] (hs_sid H) h *
  @field_at Noise.CS sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
  @field_at Noise.CS sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
  @field_at Noise.CS sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
  @field_at Noise.CS sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
  @field_at Noise.CS sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
  @field_at Noise.CS sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
  @field_at Noise.CS sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
  @field_at Noise.CS sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
  @field_at Noise.CS sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h.
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  unfold hc4nb2_hs_sbn_hsf.
  hc4nb2_hs_sbn_cc I._state (Vint (hs_state H)).
  hc4nb2_hs_sbn_cc I._last_initiation_consumption (Vlong (hs_lic H)).
  hc4nb2_hs_sbn_cc I._static_identity (hs_sid H). hc4nb2_hs_sbn_cc I._remote_index (Vint (hs_rindex H)).
  hc4nb2_hs_sbn_cc I._ephemeral_private (bytes (hs_eph H)).
  hc4nb2_hs_sbn_cc I._remote_static (bytes (hs_rstatic H)).
  hc4nb2_hs_sbn_cc I._remote_ephemeral (bytes (hs_reph H)).
  hc4nb2_hs_sbn_cc I._precomputed_static_static (bytes (hs_ss H)).
  hc4nb2_hs_sbn_cc I._preshared_key (bytes (hs_psk H)). hc4nb2_hs_sbn_cc I._hash (bytes (hs_hash H)).
  hc4nb2_hs_sbn_cc I._chaining_key (bytes (hs_ck H)). hc4nb2_hs_sbn_cc I._latest_timestamp (bytes (hs_ts H)).
  rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
    (field_at_data_at sh t_hs (DOT I._remote_static)),
    (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
    (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
    (field_at_data_at sh t_hs (DOT I._preshared_key)),
    (field_at_data_at sh t_hs (DOT I._hash)),
    (field_at_data_at sh t_hs (DOT I._chaining_key)),
    (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
  simpl nested_field_type.
  rewrite (hc4nb2_hs_sbn_hbytes sh 32 (hs_eph H)), (hc4nb2_hs_sbn_hbytes sh 32 (hs_rstatic H)),
    (hc4nb2_hs_sbn_hbytes sh 32 (hs_reph H)), (hc4nb2_hs_sbn_hbytes sh 32 (hs_ss H)),
    (hc4nb2_hs_sbn_hbytes sh 32 (hs_psk H)), (hc4nb2_hs_sbn_hbytes sh 32 (hs_hash H)),
    (hc4nb2_hs_sbn_hbytes sh 32 (hs_ck H)), (hc4nb2_hs_sbn_hbytes sh 12 (hs_ts H)) by auto.
  reflexivity.
Qed.

Lemma hc4nb2_hs_sbn_peer_eq sh p P :
  peer_rep sh p P = hc4nb2_hs_sbn_hsf sh (hs_addr p) (p_hs P) * hc4nb2_hs_sbn_prest sh p P.
Proof.
  unfold peer_rep, hs_rep, hc4nb2_hs_sbn_prest.
  apply pred_ext.
  - Intros. rewrite hc4nb2_hs_sbn_hsf_eq by auto. Intros lk. Exists lk. entailer!.
  - Intros lk. rewrite hc4nb2_hs_sbn_hsf_eq by auto. entailer!. Exists lk. cancel.
Qed.

Lemma hc4nb2_hs_sbn_fc p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_peer [] p.
Proof. intros. apply (@field_compatible_change_composite Noise.CS CSkhnb _ t_peer); auto. Qed.

Lemma hc4nb2_hs_sbn_entry_fa sh v p :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at CSkhnb sh t_hs (DOT FH._entry) v (hs_addr p).
Proof.
  intros FC0. pose proof (hc4nb2_hs_sbn_fc p FC0) as FC.
  rewrite (@data_at_change_composite Noise.CS CSkhnb _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: field_compatible t_hs (DOT FH._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hc4nb2_hs_sbn_open sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
  (@field_at CSkhnb she t_hs (DOT FH._entry) (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p) *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (hc4nb2_hs_sbn_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hc4nb2_hs_sbn_entry_fa by auto.
  apply pred_ext; entailer!.
Qed.

Lemma hc4nb2_hs_sbn_pool_ptrs L (D: list (val * share * entry)) :
  iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [|[[x sh] e] D IH]; simpl.
  - entailer!.
  - assert_PROP (Forall isptr (saddrs D)) as HF by (sep_apply IH; entailer!).
    unfold pool_item_rep at 1, entry_at.
    assert_PROP (isptr x) as Hx by (entailer!; match goal with Hc: field_compatible _ _ x |- _ => destruct Hc; auto end).
    entailer!.
Qed.

Lemma hc4nb2_hs_sbn_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

Lemma hc4nb2_hs_sbn_succ_in T a :
  itable_wf T -> succ_in (t_L T) a = nullval \/ In (succ_in (t_L T) a) (saddrs (t_D T)).
Proof.
  intros (_ & HI & _). destruct (hc4nb2_hs_sbn_succ (t_L T) a) as [-> | Hin]; auto.
Qed.

Lemma hc4nb2_hs_sbn_ptr_or_null T x :
  Forall isptr (saddrs (t_D T)) -> x = nullval \/ In x (saddrs (t_D T)) -> is_pointer_or_null x.
Proof.
  intros HF [-> | Hin]; [simpl; auto|].
  rewrite Forall_forall in HF. apply HF in Hin. destruct x; try contradiction; exact I.
Qed.

Lemma hc4nb2_hs_sbn_fch p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_hs [] (hs_addr p).
Proof.
  intros FC0. pose proof (hc4nb2_hs_sbn_fc p FC0) as FC.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

(* valid pointers for the comparisons *)
Lemma hc4nb2_hs_sbn_vp_tab sht tab T x R :
  x = nullval \/ In x (saddrs (t_D T)) -> itable sht tab T * R |-- valid_pointer x.
Proof.
  intros [-> | Ha]; [apply valid_pointer_null|].
  apply sepcon_valid_pointer1.
  destruct (hc4nb2_hs_sbn_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (hc4nb2_hs_sbn_split _ _ _ _ _ HE).
  assert (writable_share sh).
  { destruct H as (_ & _ & _ & HF). apply hc4nb2_hs_sbn_sfind_In in HE.
    rewrite Forall_forall in HF. apply (HF _ HE). }
  unfold pool_item_rep, entry_at.
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4nb2_hs_sbn_vp_peer sh p P R :
  readable_share sh -> hc4nb2_hs_sbn_prest sh p P * R |-- valid_pointer p.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold hc4nb2_hs_sbn_prest. Intros.
  do 12 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hc4nb2_hs_sbn_vp_dev sh wg D R :
  readable_share sh -> device_rep sh wg D * R |-- valid_pointer (id_addr wg).
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold device_rep, identity_rep. Intros.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply sepcon_valid_pointer2. Intros lk.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

(* a pointer comparison (both pointers or NULL) as the model's eq_dec *)
Lemma hc4nb2_hs_sbn_cmp x y : is_pointer_or_null x -> is_pointer_or_null y ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y))) =
  Val.of_bool (if eq_dec x y then true else false).
Proof.
  intros Hx Hy.
  destruct x; try contradiction; destruct y; try contradiction; simpl in Hx, Hy; subst;
  destruct (eq_dec _ _) as [Heq|Hne]; unfold sem_cmp_pp; simpl; try congruence; try reflexivity.
  - destruct (eq_block b b0); [|congruence]. subst. inv Heq. rewrite Ptrofs.eq_true. reflexivity.
  - destruct (eq_block b b0); [|reflexivity]. subst. rewrite Ptrofs.eq_false by congruence. reflexivity.
Qed.

Definition hc4nb2_hs_sbn_is (a b: val) : Prop := a = b.
Definition hc4nb2_hs_sbn_isb (a b: bool) : Prop := a = b.

Lemma hc4nb2_hs_sbn_tt (b: bool) : typed_true tint (if b then Vtrue else Vfalse) -> b = true.
Proof. destruct b; auto. intros X. inv X. Qed.
Lemma hc4nb2_hs_sbn_tf (b: bool) : typed_false tint (if b then Vtrue else Vfalse) -> b = false.
Proof. destruct b; auto. intros X. inv X. Qed.

Ltac hc4nb2_hs_sbn_fin :=
  entailer!;
  match goal with H: typed_true tint _ |- _ => apply hc4nb2_hs_sbn_tt in H; rewrite H end;
  cbn [andb];
  first [ match goal with |- Val.of_bool (Bool.eqb ?x ?y) = _ => destruct x, y; reflexivity end
        | match goal with |- Val.of_bool ?X = bool2val ?Y => change Y with X; destruct X; reflexivity end
        | match goal with |- Val.of_bool ?X = _ => destruct X; reflexivity end ].
Ltac hc4nb2_hs_sbn_fin_false :=
  entailer!;
  match goal with H: typed_false tint _ |- _ => apply hc4nb2_hs_sbn_tf in H; rewrite H end;
  reflexivity.
(* the rest of hs_mem beside the compared fields *)
Definition hc4nb2_hs_sbn_rest (whole: bool) (sh: share) (p: val) (P: peer) : mpred :=
  if whole then hc4nb2_hs_sbn_prest sh p P
  else !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
       ((EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk (hs_addr p)) *
        spacer sh 36 40 (hs_addr p) * spacer sh 300 304 (hs_addr p) *
        @field_at_ Noise.CS sh t_peer [StructField I._device] p).

Lemma hc4nb2_hs_sbn_mem_eq whole sh p P :
  hs_mem whole sh p P = hc4nb2_hs_sbn_hsf sh (hs_addr p) (p_hs P) * hc4nb2_hs_sbn_rest whole sh p P.
Proof.
  destruct whole; [apply hc4nb2_hs_sbn_peer_eq|].
  unfold hs_mem, hs_rep, hc4nb2_hs_sbn_rest. apply pred_ext.
  - Intros lk. rewrite hc4nb2_hs_sbn_hsf_eq by auto.
    assert_PROP (@field_compatible Noise.CS t_peer [StructField I._device] p) as FC by entailer!.
    entailer!.
    + destruct FC as (A1 & A2 & A3 & A4 & _). repeat split; auto.
    + Exists lk. cancel.
  - Intros lk. rewrite hc4nb2_hs_sbn_hsf_eq by auto. entailer!. Exists lk. cancel.
Qed.

Lemma hc4nb2_hs_sbn_rest_facts whole sh p P :
  hc4nb2_hs_sbn_rest whole sh p P |-- !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)).
Proof. destruct whole; unfold hc4nb2_hs_sbn_rest, hc4nb2_hs_sbn_prest; entailer!. Qed.

Lemma hc4nb2_hs_sbn_vp_rest whole sh p P R :
  readable_share sh -> hc4nb2_hs_sbn_rest whole sh p P * R |-- valid_pointer p.
Proof.
  intros RS. destruct whole; [apply hc4nb2_hs_sbn_vp_peer; auto|].
  apply sepcon_valid_pointer1. unfold hc4nb2_hs_sbn_rest. Intros.
  apply sepcon_valid_pointer2. unfold field_at_.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

(* every compared pointer: NULL, p, a pool entry of T or a lent address *)
Lemma hc4nb2_hs_sbn_vp CSw VO whole shp p P sht tab T x R :
  Forall vobj_ok VO -> readable_share shp -> readable_share sht -> vp_ok (hs_own p T VO) x ->
  hc4nb2_hs_sbn_rest whole shp p P * itable sht tab T * vobjs CSw VO * R |-- valid_pointer x.
Proof.
  intros HV RS RT [-> | Hin]; [apply valid_pointer_null|].
  unfold hs_own in Hin. destruct Hin as [<- | Hin].
  - rewrite !sepcon_assoc. apply hc4nb2_hs_sbn_vp_rest; auto.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + rewrite (sepcon_comm (hc4nb2_hs_sbn_rest _ _ _ _)). rewrite !sepcon_assoc.
      apply hc4nb2_hs_sbn_vp_itab; simpl; auto.
    + rewrite (sepcon_comm _ (vobjs CSw VO)). rewrite !sepcon_assoc.
      apply hc4nb2_hs_sbn_vp_vobjs; auto.
Qed.

Lemma hc4nb2_hs_sbn_pn CSw VO whole shp p P sht tab T x R :
  Forall vobj_ok VO -> readable_share shp -> readable_share sht -> vp_ok (hs_own p T VO) x ->
  hc4nb2_hs_sbn_rest whole shp p P * itable sht tab T * vobjs CSw VO * R |-- !! is_pointer_or_null x.
Proof.
  intros. eapply derives_trans; [apply hc4nb2_hs_sbn_vp; eauto |]. constructor. apply valid_pointer_is_pointer_or_null.
Qed.

(* the C's pointer test (both pointers or NULL) *)
Lemma hc4nb2_hs_sbn_cmp_raw x y : is_pointer_or_null x -> is_pointer_or_null y ->
  force_val (sem_cmp_pp Ceq x y) = Val.of_bool (if eq_dec x y then true else false).
Proof.
  intros Hx Hy.
  destruct x; try contradiction; destruct y; try contradiction; simpl in Hx, Hy; subst;
  destruct (eq_dec _ _) as [Heq|Hne]; unfold sem_cmp_pp; simpl; try congruence; try reflexivity.
  - destruct (eq_block b b0); [|congruence]. subst. inv Heq. rewrite Ptrofs.eq_true. reflexivity.
  - destruct (eq_block b b0); [|reflexivity]. subst. rewrite Ptrofs.eq_false by congruence. reflexivity.
Qed.

Lemma hc4nb2_hs_sbn_cmp_tt x y : is_pointer_or_null x -> is_pointer_or_null y ->
  typed_true tint (force_val (sem_cmp_pp Ceq x y)) -> x = y.
Proof.
  intros Hx Hy. rewrite (hc4nb2_hs_sbn_cmp_raw x y Hx Hy). destruct (eq_dec x y); auto.
  intros X; inv X.
Qed.

Lemma hc4nb2_hs_sbn_cmp_tf x y : is_pointer_or_null x -> is_pointer_or_null y ->
  typed_false tint (force_val (sem_cmp_pp Ceq x y)) -> x <> y.
Proof.
  intros Hx Hy. rewrite (hc4nb2_hs_sbn_cmp_raw x y Hx Hy). destruct (eq_dec x y); auto.
  intros X; inv X.
Qed.

Lemma hc4nb2_hs_sbn_eqb sn T p E H :
  snap_eqb_nn sn (snap_of T (hs_addr p) E H) =
  (veqb (e_peer (sn_entry sn)) (e_peer E) && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state H) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic H) && veqb (hs_sid (sn_hs sn)) (hs_sid H) && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph H) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic H) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph H) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss H) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk H) && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash H) && bytes_eqb (hs_ck (sn_hs sn)) (hs_ck H) && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts H) && Int.eq (hs_rindex (sn_hs sn)) (hs_rindex H))%bool.
Proof.
  unfold snap_eqb_nn, snap_of, entry_eqb, hs_eqb, veqb. cbn [sn_entry sn_next sn_hashed sn_hs].
  apply eq_true_iff_eq. rewrite !andb_true_iff. tauto.
Qed.

(* the world's compspecs, hidden from typeclass resolution *)
Definition hc4nb2_hs_sbn_csw := compspecs.
#[local] Typeclasses Opaque hc4nb2_hs_sbn_csw.

Lemma hc4nb2_hs_sbn_main (CSw: hc4nb2_hs_sbn_csw) :
  @semax_body [] hc4_G_hs_same CSkhnb FKP.f_hs_same_but_next (hs_same_but_next4_spec CSw).
Proof.
  start_function.
  rename H into HV, SH into RSs, SH0 into RSp, SH1 into RSt, H0 into HIn, H1 into HP.
  rewrite hc4nb2_hs_sbn_mem_eq.
  assert_PROP (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) as FCH.
  { sep_apply hc4nb2_hs_sbn_rest_facts. entailer!. }
  destruct FCH as [FC HOK].
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  destruct (hc4nb2_hs_sbn_sfind_in _ _ HIn) as (she & E & HS).
  assert (HE: t_entry_d T (hs_addr p) = E) by (unfold t_entry_d, t_entry; rewrite HS; reflexivity).
  unfold hs_snap_cur in *. rewrite HE in *.
  unfold hs_ptrs_nn, snap_of in HP. cbn [sn_entry sn_hs] in HP.
  rewrite !Forall_cons_iff in HP. destruct HP as (VP1 & VP2 & VP3 & VP4 & _).
  assert_PROP (is_pointer_or_null (e_peer (sn_entry sn))) as PN1 by (go_lower;
    eapply derives_trans; [| apply (hc4nb2_hs_sbn_pn CSw VO whole shp p P sht tab T _ TT); eauto]; cancel).
  assert_PROP (is_pointer_or_null (e_peer E)) as PN2 by (go_lower;
    eapply derives_trans; [| apply (hc4nb2_hs_sbn_pn CSw VO whole shp p P sht tab T _ TT); eauto]; cancel).
  assert_PROP (is_pointer_or_null (hs_sid (sn_hs sn))) as PN3 by (go_lower;
    eapply derives_trans; [| apply (hc4nb2_hs_sbn_pn CSw VO whole shp p P sht tab T _ TT); eauto]; cancel).
  assert_PROP (is_pointer_or_null (hs_sid (p_hs P))) as PN4 by (go_lower;
    eapply derives_trans; [| apply (hc4nb2_hs_sbn_pn CSw VO whole shp p P sht tab T _ TT); eauto]; cancel).
  assert_PROP (Forall isptr (saddrs (t_D T))) as PP.
  { unfold itable. Intros. sep_apply hc4nb2_hs_sbn_pool_ptrs. entailer!. }
  assert_PROP (field_compatible t_hsnap [] s /\ hs_ok (sn_hs sn)) as FCS.
  { erewrite (@data_at_change_composite HCS CSkhnb _ shs t_hsnap _ _ (JMeq_refl _)) by reflexivity.
    entailer!.
    match goal with Hv: value_fits t_hsnap _ |- _ => unfold t_hsnap, hsnap_val in Hv; simplify_value_fits in Hv;
      destruct Hv as (_ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _) end.
    simplify_value_fits in A1. simplify_value_fits in A2. simplify_value_fits in A3. simplify_value_fits in A4.
    simplify_value_fits in A5. simplify_value_fits in A6. simplify_value_fits in A7. simplify_value_fits in A8.
    unfold hs_ok, bytes in *. rewrite !Zlength_map in *. tauto. }
  destruct FCS as [FCs SOK].
  pose proof (hc4nb2_hs_sbn_fch p FC) as FCh.
  rewrite (hc4nb2_hs_sbn_open sht tab T p she E FC W HS).
  unfold hc4nb2_hs_sbn_hsf.
  unfold hsnap_val. rewrite hc4nb2_hs_sbn_snap_eq.
  pose proof SOK as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  rewrite (hc4nb2_hs_sbn_hbytes shs 32 (hs_eph (sn_hs sn))), (hc4nb2_hs_sbn_hbytes shs 32 (hs_rstatic (sn_hs sn))),
    (hc4nb2_hs_sbn_hbytes shs 32 (hs_reph (sn_hs sn))), (hc4nb2_hs_sbn_hbytes shs 32 (hs_ss (sn_hs sn))),
    (hc4nb2_hs_sbn_hbytes shs 32 (hs_psk (sn_hs sn))), (hc4nb2_hs_sbn_hbytes shs 32 (hs_hash (sn_hs sn))),
    (hc4nb2_hs_sbn_hbytes shs 32 (hs_ck (sn_hs sn))), (hc4nb2_hs_sbn_hbytes shs 12 (hs_ts (sn_hs sn))) by auto.
  repeat flatten_sepcon_in_SEP.
  unfold entry_val.
  assert (Pp: isptr p) by (destruct FC; auto).
  assert (WS: writable_share she).
  { destruct W as (_ & _ & _ & HF). apply hc4nb2_hs_sbn_sfind_In in HS.
    rewrite Forall_forall in HF. apply (HF _ HS). }
  assert (RS: readable_share she) by auto.
  forward. forward.
  assert (TB1: tc_val tbool (Val.of_bool (sn_hashed sn))) by (destruct (sn_hashed sn); hnf; auto).
  assert (TB2: tc_val tbool (Val.of_bool (vin (hs_addr p) (t_L T)))) by (destruct (vin _ _); hnf; auto).
  pose proof HOK as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  forward_if (temp FKP._t'1 (Val.of_bool (veqb (e_peer (sn_entry sn)) (e_peer E) && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T))))).
  { apply denote_tc_test_eq_split;
      (sep_apply (derives_refl' _ _ (eq_sym (hc4nb2_hs_sbn_open sht tab T p she _ FC W HS)));
       eapply derives_trans; [| apply (hc4nb2_hs_sbn_vp CSw VO whole shp p P sht tab T _ TT); auto]; cancel). }
  { forward. forward. forward. entailer!. unfold veqb.
    match goal with |- context [if ?c then true else false] => destruct c; [|congruence] end.
    destruct (sn_hashed sn), (vin (hs_addr p) (t_L T)); reflexivity. }
  { forward. entailer!. unfold veqb.
    match goal with |- context [if ?c then true else false] => destruct c; [congruence|] end. reflexivity. }
  remember ((veqb (e_peer (sn_entry sn)) (e_peer E) && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)))%bool) as b1 eqn:E1. change (hc4nb2_hs_sbn_isb b1 ((veqb (e_peer (sn_entry sn)) (e_peer E) && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)))%bool)) in E1. try deadvars!.
  forward_if (temp FKP._t'2 (Val.of_bool (b1 && Int.eq (e_type (sn_entry sn)) (e_type E)))).
  { forward. forward. forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b1 && Int.eq (e_type (sn_entry sn)) (e_type E))%bool) as b2 eqn:E2. change (hc4nb2_hs_sbn_isb b2 ((b1 && Int.eq (e_type (sn_entry sn)) (e_type E))%bool)) in E2. try deadvars!.
  forward_if (temp FKP._t'3 (Val.of_bool (b2 && Int.eq (e_index (sn_entry sn)) (e_index E)))).
  { forward. forward. forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b2 && Int.eq (e_index (sn_entry sn)) (e_index E))%bool) as b3 eqn:E3. change (hc4nb2_hs_sbn_isb b3 ((b2 && Int.eq (e_index (sn_entry sn)) (e_index E))%bool)) in E3. try deadvars!.
  forward_if (temp FKP._t'4 (Val.of_bool (b3 && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P))))).
  { forward. forward. forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b3 && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)))%bool) as b4 eqn:E4. change (hc4nb2_hs_sbn_isb b4 ((b3 && Int.eq (hs_state (sn_hs sn)) (hs_state (p_hs P)))%bool)) in E4. try deadvars!.
  forward_if (temp FKP._t'5 (Val.of_bool (b4 && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P))))).
  { forward. forward. forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b4 && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)))%bool) as b5 eqn:E5. change (hc4nb2_hs_sbn_isb b5 ((b4 && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)))%bool)) in E5. try deadvars!.
  forward_if (temp FKP._t'6 (Val.of_bool (b5 && veqb (hs_sid (sn_hs sn)) (hs_sid (p_hs P))))).
  { forward. forward. forward.
    { entailer!. apply denote_tc_test_eq_split;
      (sep_apply (derives_refl' _ _ (eq_sym (hc4nb2_hs_sbn_open sht tab T p she _ FC W HS)));
       eapply derives_trans; [| apply (hc4nb2_hs_sbn_vp CSw VO whole shp p P sht tab T _ TT); auto]; cancel). }
    entailer!. rewrite hc4nb2_hs_sbn_cmp by auto.
    match goal with H: typed_true tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc4nb2_hs_sbn_tt _ H) end.
    reflexivity. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b5 && veqb (hs_sid (sn_hs sn)) (hs_sid (p_hs P)))%bool) as b6 eqn:E6. change (hc4nb2_hs_sbn_isb b6 ((b5 && veqb (hs_sid (sn_hs sn)) (hs_sid (p_hs P)))%bool)) in E6. try deadvars!.
  forward_if (temp FKP._t'7 (Val.of_bool (b6 && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._ephemeral_private) s, hs_eph (sn_hs sn),
                  shp, field_address t_hs (DOT FH._ephemeral_private) (hs_addr p), hs_eph (p_hs P)).
    { entailer!. simpl. rewrite M1. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b6 && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)))%bool) as b7 eqn:E7. change (hc4nb2_hs_sbn_isb b7 ((b6 && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph (p_hs P)))%bool)) in E7. try deadvars!.
  forward_if (temp FKP._t'9 (Val.of_bool (b7 && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._remote_static) s, hs_rstatic (sn_hs sn),
                  shp, field_address t_hs (DOT FH._remote_static) (hs_addr p), hs_rstatic (p_hs P)).
    { entailer!. simpl. rewrite M2. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b7 && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)))%bool) as b8 eqn:E8. change (hc4nb2_hs_sbn_isb b8 ((b7 && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)))%bool)) in E8. try deadvars!.
  forward_if (temp FKP._t'11 (Val.of_bool (b8 && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._remote_ephemeral) s, hs_reph (sn_hs sn),
                  shp, field_address t_hs (DOT FH._remote_ephemeral) (hs_addr p), hs_reph (p_hs P)).
    { entailer!. simpl. rewrite M3. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b8 && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P)))%bool) as b9 eqn:E9. change (hc4nb2_hs_sbn_isb b9 ((b8 && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph (p_hs P)))%bool)) in E9. try deadvars!.
  forward_if (temp FKP._t'13 (Val.of_bool (b9 && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._precomputed_static_static) s, hs_ss (sn_hs sn),
                  shp, field_address t_hs (DOT FH._precomputed_static_static) (hs_addr p), hs_ss (p_hs P)).
    { entailer!. simpl. rewrite M4. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b9 && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)))%bool) as b10 eqn:E10. change (hc4nb2_hs_sbn_isb b10 ((b9 && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)))%bool)) in E10. try deadvars!.
  forward_if (temp FKP._t'15 (Val.of_bool (b10 && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._preshared_key) s, hs_psk (sn_hs sn),
                  shp, field_address t_hs (DOT FH._preshared_key) (hs_addr p), hs_psk (p_hs P)).
    { entailer!. simpl. rewrite M5. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b10 && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P)))%bool) as b11 eqn:E11. change (hc4nb2_hs_sbn_isb b11 ((b10 && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P)))%bool)) in E11. try deadvars!.
  forward_if (temp FKP._t'17 (Val.of_bool (b11 && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._hash) s, hs_hash (sn_hs sn),
                  shp, field_address t_hs (DOT FH._hash) (hs_addr p), hs_hash (p_hs P)).
    { entailer!. simpl. rewrite M6. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b11 && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash (p_hs P)))%bool) as b12 eqn:E12. change (hc4nb2_hs_sbn_isb b12 ((b11 && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash (p_hs P)))%bool)) in E12. try deadvars!.
  forward_if (temp FKP._t'19 (Val.of_bool (b12 && bytes_eqb (hs_ck (sn_hs sn)) (hs_ck (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._chaining_key) s, hs_ck (sn_hs sn),
                  shp, field_address t_hs (DOT FH._chaining_key) (hs_addr p), hs_ck (p_hs P)).
    { entailer!. simpl. rewrite M7. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b12 && bytes_eqb (hs_ck (sn_hs sn)) (hs_ck (p_hs P)))%bool) as b13 eqn:E13. change (hc4nb2_hs_sbn_isb b13 ((b12 && bytes_eqb (hs_ck (sn_hs sn)) (hs_ck (p_hs P)))%bool)) in E13. try deadvars!.
  forward_if (temp FKP._t'21 (Val.of_bool (b13 && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._latest_timestamp) s, hs_ts (sn_hs sn),
                  shp, field_address t_hs (DOT FH._latest_timestamp) (hs_addr p), hs_ts (p_hs P)).
    { entailer!. simpl. rewrite M8. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b13 && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts (p_hs P)))%bool) as b14 eqn:E14. change (hc4nb2_hs_sbn_isb b14 ((b13 && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts (p_hs P)))%bool)) in E14. try deadvars!.
  forward_if (temp FKP._t'23 (Val.of_bool (b14 && Int.eq (hs_rindex (sn_hs sn)) (hs_rindex (p_hs P))))).
  { forward. forward. forward. hc4nb2_hs_sbn_fin. }
  { forward. hc4nb2_hs_sbn_fin_false. }
  remember ((b14 && Int.eq (hs_rindex (sn_hs sn)) (hs_rindex (p_hs P)))%bool) as b15 eqn:E15. change (hc4nb2_hs_sbn_isb b15 ((b14 && Int.eq (hs_rindex (sn_hs sn)) (hs_rindex (p_hs P)))%bool)) in E15. try deadvars!.
  forward.
  unfold hsnap_val. rewrite hc4nb2_hs_sbn_snap_eq.
  rewrite (hc4nb2_hs_sbn_hbytes shs 32 (hs_eph (sn_hs sn))), (hc4nb2_hs_sbn_hbytes shs 32 (hs_rstatic (sn_hs sn))),
    (hc4nb2_hs_sbn_hbytes shs 32 (hs_reph (sn_hs sn))), (hc4nb2_hs_sbn_hbytes shs 32 (hs_ss (sn_hs sn))),
    (hc4nb2_hs_sbn_hbytes shs 32 (hs_psk (sn_hs sn))), (hc4nb2_hs_sbn_hbytes shs 32 (hs_hash (sn_hs sn))),
    (hc4nb2_hs_sbn_hbytes shs 32 (hs_ck (sn_hs sn))), (hc4nb2_hs_sbn_hbytes shs 12 (hs_ts (sn_hs sn))) by auto.
  rewrite hc4nb2_hs_sbn_mem_eq. unfold hc4nb2_hs_sbn_hsf.
  rewrite (hc4nb2_hs_sbn_open sht tab T p she _ FC W HS). unfold entry_val.
  rewrite (hc4nb2_hs_sbn_eqb sn T p _ (p_hs P)).
  unfold hc4nb2_hs_sbn_isb in E15, E14, E13, E12, E11, E10, E9, E8, E7, E6, E5, E4, E3, E2, E1.
  rewrite <- E1, <- E2, <- E3, <- E4, <- E5, <- E6, <- E7, <- E8, <- E9, <- E10, <- E11, <- E12, <- E13, <- E14, <- E15.
  clear E15 E14 E13 E12 E11 E10 E9 E8 E7 E6 E5 E4 E3 E2 E1.
  entailer!.
  destruct b15; reflexivity.
Qed.

Lemma hc4nb2_hs_sbn_body :
  forall CSw, @semax_body [] hc4_G_hs_same CSkhnb WgNoise.harness.x_keypairs.code.f_hs_same_but_next (hs_same_but_next4_spec CSw).
Proof.
  intros CSw. exact (hc4nb2_hs_sbn_main CSw).
Qed.
