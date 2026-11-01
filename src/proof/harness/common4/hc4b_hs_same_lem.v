(* (common4 group hs, hs_same): helpers of the body of hs_same at the v4 spec,
   adapted from v1's hc3b_snap_same_* (hc3_body_snap.v).  The compared pointers are NULL, p, a pool entry of T or
   an address of the lent objects (hc4b_hs_same_vp). *)
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
Require WgNoise.harness.x_handshake.code.

Module FH := WgNoise.harness.x_handshake.code.
Local Open Scope logic.

(* ---- the lent objects' addresses are valid pointers ---- *)
Section VP.
#[local] Existing Instance Noise.CS.

Lemma hc4b_hs_same_vp_peer sh p P R :
  readable_share sh -> peer_rep sh p P * R |-- valid_pointer p.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold peer_rep. Intros.
  do 10 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hc4b_hs_same_vp_peers PS x R :
  Forall (fun x => match x with (_, sh, _) => readable_share sh end) PS -> In x (map peer_addr4 PS) ->
  peers_rep PS * R |-- valid_pointer x.
Proof.
  revert R. induction PS as [|[[a sh] P] PS IH]; simpl; intros R HF Hin; [contradiction|].
  inversion HF; subst. unfold peers_rep in *. simpl iter_sepcon. destruct Hin as [<- | Hin].
  - rewrite sepcon_assoc. apply hc4b_hs_same_vp_peer; auto.
  - rewrite sepcon_assoc, (sepcon_comm (peer_rep sh a P)), sepcon_assoc. apply IH; auto.
Qed.

Lemma hc4b_hs_same_vp_dev sh wg D x R :
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

Lemma hc4b_hs_same_saddrs_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct H as [<- | H]; [eauto|]. destruct (IH H) as (sh & E & HI). eauto.
Qed.

Lemma hc4b_hs_same_vp_itab sh tab T x R :
  readable_share sh -> In x (tab :: saddrs (t_D T)) -> itable sh tab T * R |-- valid_pointer x.
Proof.
  intros RS [<- | Hin].
  - apply sepcon_valid_pointer1. unfold itable. Intros. apply sepcon_valid_pointer1.
    apply data_at_valid_ptr; [auto | simpl; lia].
  - apply sepcon_valid_pointer1. unfold itable. Intros. apply sepcon_valid_pointer2.
    destruct (hc4b_hs_same_saddrs_in _ _ Hin) as (shx & E & HE).
    eapply derives_trans; [apply iter_sepcon_in_true; exact HE|].
    apply sepcon_valid_pointer1. unfold pool_item_rep, entry_at.
    assert (writable_share shx).
    { destruct H as (_ & _ & _ & HF). rewrite Forall_forall in HF. apply (HF _ HE). }
    apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

(* v4.1: kents and keypairs lend no address (their byte 0 is an index-table entry) *)
Lemma hc4b_hs_same_vp_obj CSw o x R :
  vobj_ok o -> In x (vobj_addrs o) -> vobj_rep CSw o * R |-- valid_pointer x.
Proof.
  intros OK Hin.
  destruct o; simpl in OK, Hin |- *; try contradiction.
  - destruct Hin as [<- | []]. apply hc4b_hs_same_vp_peer; auto.
  - apply hc4b_hs_same_vp_peers; auto.
  - apply hc4b_hs_same_vp_dev; auto.
  - apply hc4b_hs_same_vp_itab; auto.
  - destruct Hin as [<- | []]. destruct OK as [RS LEN]. apply sepcon_valid_pointer1.
    unfold bytes_at. apply data_at_valid_ptr; [auto | simpl; rewrite Z.max_r by lia; lia].
  - destruct Hin as [<- | []]. destruct OK as [RS LEN]. apply sepcon_valid_pointer1.
    apply memory_block_valid_ptr; [auto | lia].
  - destruct Hin as [<- | []]. apply sepcon_valid_pointer1.
    apply malloc_token_valid_pointer. apply (OK CSw).
Qed.

Lemma hc4b_hs_same_vp_vobjs CSw VO x R :
  Forall vobj_ok VO -> In x (vobjs_addrs VO) -> vobjs CSw VO * R |-- valid_pointer x.
Proof.
  revert R. induction VO as [|o VO IH]; simpl; intros R HF Hin; [contradiction|].
  inversion HF; subst. unfold vobjs_addrs in Hin. simpl in Hin. apply in_app_or in Hin.
  unfold vobjs. simpl iter_sepcon. destruct Hin as [Hin | Hin].
  - rewrite sepcon_assoc. apply hc4b_hs_same_vp_obj; auto.
  - rewrite sepcon_assoc, (sepcon_comm (vobj_rep CSw o)), sepcon_assoc. apply IH; auto.
Qed.
End VP.

(* ---- the snapshot struct and the handshake's fields at CSkh (v1) ---- *)
Section Helpers.
#[local] Existing Instance CSkh.
#[local] Instance hc4b_hs_same_i1 : change_composite_env HCS CSkh. make_cs_preserve HCS CSkh. Defined.
#[local] Instance hc4b_hs_same_i2 : change_composite_env CSkh HCS. make_cs_preserve CSkh HCS. Defined.
#[local] Instance hc4b_hs_same_i3 : change_composite_env Noise.CS CSkh. make_cs_preserve Noise.CS CSkh. Defined.
#[local] Instance hc4b_hs_same_i4 : change_composite_env CSkh Noise.CS. make_cs_preserve CSkh Noise.CS. Defined.

Lemma hc4b_hs_same_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
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

Lemma hc4b_hs_same_snap_eq shs (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
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
  rewrite (@data_at_change_composite HCS CSkh _ shs t_hsnap _ _ (JMeq_refl _)) by reflexivity.
  match goal with |- @data_at _ _ _ ?v _ = _ => set (V := v) end.
  unfold data_at. rewrite (@field_at_Tstruct CSkh shs t_hsnap [] FH._hs_snap noattr V V s eq_refl (JMeq_refl _)).
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

Lemma hc4b_hs_same_hbytes sh n A x :
  Zlength A = n -> @data_at CSkh sh (tarray tuchar n) (bytes A) x = hbytes sh A x.
Proof. intros <-. unfold hbytes. apply hc4b_hs_same_data_at_cs. Qed.

Lemma hc4b_hs_same_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hc4b_hs_same_sfind_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma hc4b_hs_same_sfind_In (D: list (val * share * entry)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

(* the handshake's compared fields (at CSkh, the arrays as hbytes) *)
Definition hc4b_hs_same_hsf (sh: share) (h: val) (H: handshake) : mpred :=
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

Local Ltac hc4b_hs_same_cc f v :=
  rewrite (@field_at_change_composite Noise.CS CSkh _ _ t_hs (DOT f) v v (JMeq_refl v)) by reflexivity.

Lemma hc4b_hs_same_hsf_eq sh h H :
  hs_ok H ->
  hc4b_hs_same_hsf sh h H =
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
  unfold hc4b_hs_same_hsf.
  hc4b_hs_same_cc I._state (Vint (hs_state H)).
  hc4b_hs_same_cc I._last_initiation_consumption (Vlong (hs_lic H)).
  hc4b_hs_same_cc I._static_identity (hs_sid H). hc4b_hs_same_cc I._remote_index (Vint (hs_rindex H)).
  hc4b_hs_same_cc I._ephemeral_private (bytes (hs_eph H)).
  hc4b_hs_same_cc I._remote_static (bytes (hs_rstatic H)).
  hc4b_hs_same_cc I._remote_ephemeral (bytes (hs_reph H)).
  hc4b_hs_same_cc I._precomputed_static_static (bytes (hs_ss H)).
  hc4b_hs_same_cc I._preshared_key (bytes (hs_psk H)). hc4b_hs_same_cc I._hash (bytes (hs_hash H)).
  hc4b_hs_same_cc I._chaining_key (bytes (hs_ck H)). hc4b_hs_same_cc I._latest_timestamp (bytes (hs_ts H)).
  rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
    (field_at_data_at sh t_hs (DOT I._remote_static)),
    (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
    (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
    (field_at_data_at sh t_hs (DOT I._preshared_key)),
    (field_at_data_at sh t_hs (DOT I._hash)),
    (field_at_data_at sh t_hs (DOT I._chaining_key)),
    (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
  simpl nested_field_type.
  rewrite (hc4b_hs_same_hbytes sh 32 (hs_eph H)), (hc4b_hs_same_hbytes sh 32 (hs_rstatic H)),
    (hc4b_hs_same_hbytes sh 32 (hs_reph H)), (hc4b_hs_same_hbytes sh 32 (hs_ss H)),
    (hc4b_hs_same_hbytes sh 32 (hs_psk H)), (hc4b_hs_same_hbytes sh 32 (hs_hash H)),
    (hc4b_hs_same_hbytes sh 32 (hs_ck H)), (hc4b_hs_same_hbytes sh 12 (hs_ts H)) by auto.
  reflexivity.
Qed.

(* the rest of hs_mem: the peer's first field (p valid), the lock and padding of the handshake, and (whole)
   the rest of the peer *)
Definition hc4b_hs_same_other (sh: share) (p: val) (P: peer) : mpred :=
  @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
  @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Definition hc4b_hs_same_rest (whole: bool) (sh: share) (p: val) (P: peer) : mpred :=
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
  ((if whole then @field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p
    else @field_at_ Noise.CS sh t_peer [StructField I._device] p) *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk (hs_addr p)) *
   spacer sh 36 40 (hs_addr p) * spacer sh 300 304 (hs_addr p) *
   (if whole then hc4b_hs_same_other sh p P else emp)).

Lemma hc4b_hs_same_mem_eq whole sh p P :
  hs_mem whole sh p P = hc4b_hs_same_hsf sh (hs_addr p) (p_hs P) * hc4b_hs_same_rest whole sh p P.
Proof.
  unfold hs_mem, hc4b_hs_same_rest, hc4b_hs_same_other. destruct whole.
  - unfold peer_rep, hs_rep. apply pred_ext.
    + Intros lk. rewrite hc4b_hs_same_hsf_eq by auto. entailer!. Exists lk. cancel.
    + Intros lk. rewrite hc4b_hs_same_hsf_eq by auto. entailer!. Exists lk. cancel.
  - unfold hs_rep. apply pred_ext.
    + Intros lk. rewrite hc4b_hs_same_hsf_eq by auto.
      assert_PROP (@field_compatible Noise.CS t_peer [StructField I._device] p) as FC
        by (unfold field_at_; entailer!).
      Exists lk. entailer!.
      destruct FC as (A1 & A2 & A3 & A4 & _). repeat split; auto.
    + Intros lk. rewrite hc4b_hs_same_hsf_eq by auto. entailer!. Exists lk. cancel.
Qed.

Lemma hc4b_hs_same_vp_rest whole sh p P R :
  readable_share sh -> hc4b_hs_same_rest whole sh p P * R |-- valid_pointer p.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold hc4b_hs_same_rest. Intros.
  do 4 apply sepcon_valid_pointer1.
  destruct whole; [| unfold field_at_];
  apply field_at_valid_ptr0; auto; simpl; try lia; reflexivity.
Qed.

Lemma hc4b_hs_same_fc p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_peer [] p.
Proof. intros. apply (@field_compatible_change_composite Noise.CS CSkh _ t_peer); auto. Qed.

Lemma hc4b_hs_same_entry_fa sh v p :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at CSkh sh t_hs (DOT FH._entry) v (hs_addr p).
Proof.
  intros FC0. pose proof (hc4b_hs_same_fc p FC0) as FC.
  rewrite (@data_at_change_composite Noise.CS CSkh _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: field_compatible t_hs (DOT FH._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hc4b_hs_same_open sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
  (@field_at CSkh she t_hs (DOT FH._entry) (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p) *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (hc4b_hs_same_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hc4b_hs_same_entry_fa by auto.
  apply pred_ext; entailer!.
Qed.

Lemma hc4b_hs_same_pool_ptrs L (D: list (val * share * entry)) :
  iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [|[[x sh] e] D IH]; simpl.
  - entailer!.
  - assert_PROP (Forall isptr (saddrs D)) as HF by (sep_apply IH; entailer!).
    unfold pool_item_rep at 1, entry_at.
    assert_PROP (isptr x) as Hx by (entailer!; match goal with Hc: field_compatible _ _ x |- _ => destruct Hc; auto end).
    entailer!.
Qed.

Lemma hc4b_hs_same_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

Lemma hc4b_hs_same_fch p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_hs [] (hs_addr p).
Proof.
  intros FC0. pose proof (hc4b_hs_same_fc p FC0) as FC.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

(* a pointer comparison (both pointers or NULL) as the model's eq_dec *)
Lemma hc4b_hs_same_cmp x y : is_pointer_or_null x -> is_pointer_or_null y ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y))) =
  Val.of_bool (if eq_dec x y then true else false).
Proof.
  intros Hx Hy.
  destruct x; try contradiction; destruct y; try contradiction; simpl in Hx, Hy; subst;
  destruct (eq_dec _ _) as [Heq|Hne]; unfold sem_cmp_pp; simpl; try congruence; try reflexivity.
  - destruct (eq_block b b0); [|congruence]. subst. inv Heq. rewrite Ptrofs.eq_true. reflexivity.
  - destruct (eq_block b b0); [|reflexivity]. subst. rewrite Ptrofs.eq_false by congruence. reflexivity.
Qed.

Lemma hc4b_hs_same_cmp0 x y : is_pointer_or_null x -> is_pointer_or_null y ->
  force_val (sem_cmp_pp Ceq x y) = (if (if eq_dec x y then true else false) then Vtrue else Vfalse).
Proof.
  intros Hx Hy.
  destruct x; try contradiction; destruct y; try contradiction; simpl in Hx, Hy; subst;
  destruct (eq_dec _ _) as [Heq|Hne]; unfold sem_cmp_pp; simpl; try congruence; try reflexivity.
  - destruct (eq_block b b0); [|congruence]. subst. inv Heq. rewrite Ptrofs.eq_true. reflexivity.
  - destruct (eq_block b b0); [|reflexivity]. subst. rewrite Ptrofs.eq_false by congruence. reflexivity.
Qed.

Definition hc4b_hs_same_isb (a b: bool) : Prop := a = b.

Lemma hc4b_hs_same_tt (b: bool) : typed_true tint (if b then Vtrue else Vfalse) -> b = true.
Proof. destruct b; auto. intros X. inv X. Qed.
Lemma hc4b_hs_same_tf (b: bool) : typed_false tint (if b then Vtrue else Vfalse) -> b = false.
Proof. destruct b; auto. intros X. inv X. Qed.

Lemma hc4b_hs_same_eqb sn T p E H bp b1 bs :
  bp = (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) ->
  b1 = (if eq_dec (sn_next sn) (succ_in (t_L T) (hs_addr p)) then true else false) ->
  bs = (if eq_dec (hs_sid (sn_hs sn)) (hs_sid H) then true else false) ->
  snap_eqb sn (snap_of T (hs_addr p) E H) =
  (bp && b1 && Bool.eqb (sn_hashed sn) (vin (hs_addr p) (t_L T)) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int.eq (e_index (sn_entry sn)) (e_index E) && Int.eq (hs_state (sn_hs sn)) (hs_state H) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic H) && bs && bytes_eqb (hs_eph (sn_hs sn)) (hs_eph H) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic H) && bytes_eqb (hs_reph (sn_hs sn)) (hs_reph H) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss H) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk H) && bytes_eqb (hs_hash (sn_hs sn)) (hs_hash H) && bytes_eqb (hs_ck (sn_hs sn)) (hs_ck H) && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts H) && Int.eq (hs_rindex (sn_hs sn)) (hs_rindex H))%bool.
Proof.
  intros B0 B1 B2. subst bp b1 bs.
  unfold snap_eqb, snap_of, entry_eqb, hs_eqb. cbn [sn_entry sn_next sn_hashed sn_hs].
  apply eq_true_iff_eq. rewrite !andb_true_iff. tauto.
Qed.

(* the valid pointers of the comparisons: NULL, p, a pool entry of T, a lent object's address *)
Lemma hc4b_hs_same_vp CSw VO whole shp p P sht tab T x R :
  Forall vobj_ok VO -> readable_share shp -> readable_share sht -> vp_ok (hs_own p T VO) x ->
  hc4b_hs_same_rest whole shp p P * itable sht tab T * @vobjs CSw VO * R |-- valid_pointer x.
Proof.
  intros HV RP RT [-> | Hin]; [apply valid_pointer_null|].
  unfold hs_own in Hin. destruct Hin as [<- | Hin].
  { rewrite !sepcon_assoc. apply hc4b_hs_same_vp_rest; auto. }
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - rewrite (sepcon_comm (hc4b_hs_same_rest _ _ _ _)), !sepcon_assoc.
    apply hc4b_hs_same_vp_itab; simpl; auto.
  - rewrite (sepcon_comm (_ * _) (vobjs CSw VO)), !sepcon_assoc.
    apply hc4b_hs_same_vp_vobjs; auto.
Qed.

Lemma hc4b_hs_same_vp_pn CSw VO whole shp p P sht tab T x R :
  Forall vobj_ok VO -> readable_share shp -> readable_share sht -> vp_ok (hs_own p T VO) x ->
  hc4b_hs_same_rest whole shp p P * itable sht tab T * @vobjs CSw VO * R |-- !! is_pointer_or_null x.
Proof.
  intros. eapply derives_trans; [apply hc4b_hs_same_vp; eauto|]. constructor; apply valid_pointer_is_pointer_or_null.
Qed.

End Helpers.
