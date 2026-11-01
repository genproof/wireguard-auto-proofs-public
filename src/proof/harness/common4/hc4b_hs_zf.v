(* (common4 group hs): body of hs_zeroed_from (v4 spec), closes hc4_body_hs_zeroed_from *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.

Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import VST.msl.iter_sepcon.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_keypairs.code.

(* helpers adapted from v1's hc3b_snap_zf.v (proved for hs_zeroed_from_spec) *)
#[local] Existing Instance CSkh.
#[local] Instance hc4b_hs_zf_i1 : change_composite_env HCS CSkh. make_cs_preserve HCS CSkh. Defined.
#[local] Instance hc4b_hs_zf_i2 : change_composite_env CSkh HCS. make_cs_preserve CSkh HCS. Defined.
#[local] Instance hc4b_hs_zf_i3 : change_composite_env Noise.CS CSkh. make_cs_preserve Noise.CS CSkh. Defined.
#[local] Instance hc4b_hs_zf_i4 : change_composite_env CSkh Noise.CS. make_cs_preserve CSkh Noise.CS. Defined.

Lemma hc4b_hs_zf_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
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
Definition hc4b_hs_zf_ths := Tstruct FH._noise_handshake noattr.

Lemma hc4b_hs_zf_snap_eq shs (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
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

Lemma hc4b_hs_zf_hbytes sh n A x :
  Zlength A = n -> @data_at CSkh sh (tarray tuchar n) (bytes A) x = hbytes sh A x.
Proof. intros <-. unfold hbytes. apply hc4b_hs_zf_data_at_cs. Qed.

Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.

Lemma hc4b_hs_zf_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hc4b_hs_zf_sfind_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma hc4b_hs_zf_sfind_In (D: list (val * share * entry)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Definition hc4b_hs_zf_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Definition hc4b_hs_zf_hsf (sh: share) (h: val) (H: handshake) : mpred :=
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

Local Ltac hc4b_hs_zf_cc f v :=
  rewrite (@field_at_change_composite Noise.CS CSkh _ _ t_hs (DOT f) v v (JMeq_refl v)) by reflexivity.

Lemma hc4b_hs_zf_hsf_eq sh h H :
  hs_ok H ->
  hc4b_hs_zf_hsf sh h H =
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
  unfold hc4b_hs_zf_hsf.
  hc4b_hs_zf_cc I._state (Vint (hs_state H)).
  hc4b_hs_zf_cc I._last_initiation_consumption (Vlong (hs_lic H)).
  hc4b_hs_zf_cc I._static_identity (hs_sid H). hc4b_hs_zf_cc I._remote_index (Vint (hs_rindex H)).
  hc4b_hs_zf_cc I._ephemeral_private (bytes (hs_eph H)).
  hc4b_hs_zf_cc I._remote_static (bytes (hs_rstatic H)).
  hc4b_hs_zf_cc I._remote_ephemeral (bytes (hs_reph H)).
  hc4b_hs_zf_cc I._precomputed_static_static (bytes (hs_ss H)).
  hc4b_hs_zf_cc I._preshared_key (bytes (hs_psk H)). hc4b_hs_zf_cc I._hash (bytes (hs_hash H)).
  hc4b_hs_zf_cc I._chaining_key (bytes (hs_ck H)). hc4b_hs_zf_cc I._latest_timestamp (bytes (hs_ts H)).
  rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
    (field_at_data_at sh t_hs (DOT I._remote_static)),
    (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
    (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
    (field_at_data_at sh t_hs (DOT I._preshared_key)),
    (field_at_data_at sh t_hs (DOT I._hash)),
    (field_at_data_at sh t_hs (DOT I._chaining_key)),
    (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
  simpl nested_field_type.
  rewrite (hc4b_hs_zf_hbytes sh 32 (hs_eph H)), (hc4b_hs_zf_hbytes sh 32 (hs_rstatic H)),
    (hc4b_hs_zf_hbytes sh 32 (hs_reph H)), (hc4b_hs_zf_hbytes sh 32 (hs_ss H)),
    (hc4b_hs_zf_hbytes sh 32 (hs_psk H)), (hc4b_hs_zf_hbytes sh 32 (hs_hash H)),
    (hc4b_hs_zf_hbytes sh 32 (hs_ck H)), (hc4b_hs_zf_hbytes sh 12 (hs_ts H)) by auto.
  reflexivity.
Qed.

Lemma hc4b_hs_zf_peer_eq sh p P :
  peer_rep sh p P = hc4b_hs_zf_hsf sh (hs_addr p) (p_hs P) * hc4b_hs_zf_prest sh p P.
Proof.
  unfold peer_rep, hs_rep, hc4b_hs_zf_prest.
  apply pred_ext.
  - Intros. rewrite hc4b_hs_zf_hsf_eq by auto. Intros lk. Exists lk. entailer!.
  - Intros lk. rewrite hc4b_hs_zf_hsf_eq by auto. entailer!. Exists lk. cancel.
Qed.

Lemma hc4b_hs_zf_fc p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_peer [] p.
Proof. intros. apply (@field_compatible_change_composite Noise.CS CSkh _ t_peer); auto. Qed.

Lemma hc4b_hs_zf_entry_fa sh v p :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at CSkh sh t_hs (DOT FH._entry) v (hs_addr p).
Proof.
  intros FC0. pose proof (hc4b_hs_zf_fc p FC0) as FC.
  rewrite (@data_at_change_composite Noise.CS CSkh _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: field_compatible t_hs (DOT FH._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hc4b_hs_zf_open sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
  (@field_at CSkh she t_hs (DOT FH._entry) (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p) *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (hc4b_hs_zf_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hc4b_hs_zf_entry_fa by auto.
  apply pred_ext; entailer!.
Qed.

Lemma hc4b_hs_zf_pool_ptrs L (D: list (val * share * entry)) :
  iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [|[[x sh] e] D IH]; simpl.
  - entailer!.
  - assert_PROP (Forall isptr (saddrs D)) as HF by (sep_apply IH; entailer!).
    unfold pool_item_rep at 1, entry_at.
    assert_PROP (isptr x) as Hx by (entailer!; match goal with Hc: field_compatible _ _ x |- _ => destruct Hc; auto end).
    entailer!.
Qed.

Lemma hc4b_hs_zf_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

Lemma hc4b_hs_zf_succ_in T a :
  itable_wf T -> succ_in (t_L T) a = nullval \/ In (succ_in (t_L T) a) (saddrs (t_D T)).
Proof.
  intros (_ & HI & _). destruct (hc4b_hs_zf_succ (t_L T) a) as [-> | Hin]; auto.
Qed.

Lemma hc4b_hs_zf_ptr_or_null T x :
  Forall isptr (saddrs (t_D T)) -> x = nullval \/ In x (saddrs (t_D T)) -> is_pointer_or_null x.
Proof.
  intros HF [-> | Hin]; [simpl; auto|].
  rewrite Forall_forall in HF. apply HF in Hin. destruct x; try contradiction; exact I.
Qed.

Lemma hc4b_hs_zf_fch p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_hs [] (hs_addr p).
Proof.
  intros FC0. pose proof (hc4b_hs_zf_fc p FC0) as FC.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

(* valid pointers for the comparisons *)
Lemma hc4b_hs_zf_vp_tab sht tab T x R :
  x = nullval \/ In x (saddrs (t_D T)) -> itable sht tab T * R |-- valid_pointer x.
Proof.
  intros [-> | Ha]; [apply valid_pointer_null|].
  apply sepcon_valid_pointer1.
  destruct (hc4b_hs_zf_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (hc4b_hs_zf_split _ _ _ _ _ HE).
  assert (writable_share sh).
  { destruct H as (_ & _ & _ & HF). apply hc4b_hs_zf_sfind_In in HE.
    rewrite Forall_forall in HF. apply (HF _ HE). }
  unfold pool_item_rep, entry_at.
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4b_hs_zf_vp_peer sh p P R :
  readable_share sh -> hc4b_hs_zf_prest sh p P * R |-- valid_pointer p.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold hc4b_hs_zf_prest. Intros.
  do 12 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hc4b_hs_zf_vp_dev sh wg D R :
  readable_share sh -> device_rep sh wg D * R |-- valid_pointer (id_addr wg).
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold device_rep, identity_rep. Intros.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply sepcon_valid_pointer2. Intros lk.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.
(* a pointer comparison (both pointers or NULL) as the model's eq_dec *)
Lemma hc4b_hs_zf_cmp x y : is_pointer_or_null x -> is_pointer_or_null y ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y))) =
  Val.of_bool (if eq_dec x y then true else false).
Proof.
  intros Hx Hy.
  destruct x; try contradiction; destruct y; try contradiction; simpl in Hx, Hy; subst;
  destruct (eq_dec _ _) as [Heq|Hne]; unfold sem_cmp_pp; simpl; try congruence; try reflexivity.
  - destruct (eq_block b b0); [|congruence]. subst. inv Heq. rewrite Ptrofs.eq_true. reflexivity.
  - destruct (eq_block b b0); [|reflexivity]. subst. rewrite Ptrofs.eq_false by congruence. reflexivity.
Qed.

Definition hc4b_hs_zf_is (a b: val) : Prop := a = b.
Definition hc4b_hs_zf_isb (a b: bool) : Prop := a = b.
Definition hc4b_hs_zf_ise (a b: entry) : Prop := a = b.

Lemma hc4b_hs_zf_tt (b: bool) : typed_true tint (if b then Vtrue else Vfalse) -> b = true.
Proof. destruct b; auto. intros X. inv X. Qed.
Lemma hc4b_hs_zf_tf (b: bool) : typed_false tint (if b then Vtrue else Vfalse) -> b = false.
Proof. destruct b; auto. intros X. inv X. Qed.

Lemma hc4b_hs_zf_ofb (b: bool) :
  Val.of_bool b = Vint (if Int.eq (if b then Int.one else Int.zero) Int.zero then Int.zero else Int.one).
Proof. destruct b; reflexivity. Qed.

Ltac hc4b_hs_zf_fin :=
  entailer!; try unfold eq_dec in *;
  match goal with H: typed_true tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc4b_hs_zf_tt _ H) end;
  cbn [andb];
  first [apply hc4b_hs_zf_ofb | idtac];
  repeat match goal with |- context [Bool.eqb ?x ?y] => destruct x; destruct y end;
  simpl; unfold Val.of_bool;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Ltac hc4b_hs_zf_fin_false :=
  entailer!; try unfold eq_dec in *;
  match goal with H: typed_false tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc4b_hs_zf_tf _ H) end;
  reflexivity.

(* ---- v4: hs_mem (whole or not) ---- *)
Definition hc4b_hs_zf_rest (whole: bool) (sh: share) (p: val) (P: peer) : mpred :=
  if whole then hc4b_hs_zf_prest sh p P
  else !! hs_ok (p_hs P) &&
       ((EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk (hs_addr p)) *
        spacer sh 36 40 (hs_addr p) * spacer sh 300 304 (hs_addr p) *
        @field_at_ Noise.CS sh t_peer [StructField I._device] p).

Lemma hc4b_hs_zf_mem_eq whole sh p P :
  hs_mem whole sh p P = hc4b_hs_zf_hsf sh (hs_addr p) (p_hs P) * hc4b_hs_zf_rest whole sh p P.
Proof.
  destruct whole; unfold hs_mem, hc4b_hs_zf_rest; [apply hc4b_hs_zf_peer_eq|].
  unfold hs_rep. apply pred_ext.
  - Intros. rewrite hc4b_hs_zf_hsf_eq by auto. Intros lk. entailer!. Exists lk. cancel.
  - Intros. rewrite hc4b_hs_zf_hsf_eq by auto. Intros lk. entailer!. Exists lk. cancel.
Qed.

Lemma hc4b_hs_zf_rest_props whole sh p P :
  hc4b_hs_zf_rest whole sh p P |-- !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)).
Proof.
  destruct whole; unfold hc4b_hs_zf_rest.
  - unfold hc4b_hs_zf_prest. entailer!.
  - Intros lk. unfold field_at_. entailer!.
    match goal with Hc: field_compatible t_peer _ p |- _ => destruct Hc as (A1 & A2 & A3 & A4 & A5) end.
    repeat split; auto.
Qed.

Lemma hc4b_hs_zf_rest_vp whole sh p P :
  readable_share sh -> hc4b_hs_zf_rest whole sh p P |-- valid_pointer p.
Proof.
  intros RS. destruct whole; unfold hc4b_hs_zf_rest.
  - rewrite <- (sepcon_emp (hc4b_hs_zf_prest sh p P)). apply hc4b_hs_zf_vp_peer; auto.
  - Intros. apply sepcon_valid_pointer2. unfold field_at_.
    apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

(* ---- valid pointers of the lent objects ---- *)
Lemma hc4b_hs_zf_vp_peer_rep sh p P :
  readable_share sh -> peer_rep sh p P |-- valid_pointer p.
Proof.
  intros RS. rewrite hc4b_hs_zf_peer_eq. apply sepcon_valid_pointer2.
  rewrite <- (sepcon_emp (hc4b_hs_zf_prest sh p P)). apply hc4b_hs_zf_vp_peer; auto.
Qed.

Lemma hc4b_hs_zf_vp_itab sht tab T x :
  readable_share sht -> x = tab \/ In x (saddrs (t_D T)) -> itable sht tab T |-- valid_pointer x.
Proof.
  intros RS [-> | Ha].
  - unfold itable. Intros. apply sepcon_valid_pointer1.
    apply data_at_valid_ptr; [auto | simpl; lia].
  - rewrite <- (sepcon_emp (itable sht tab T)). apply hc4b_hs_zf_vp_tab. auto.
Qed.

Lemma hc4b_hs_zf_vp_peers (PS: list (val * share * peer)) x :
  In x (map peer_addr4 PS) -> Forall (fun x => match x with (_, sh, _) => readable_share sh end) PS ->
  peers_rep PS |-- valid_pointer x.
Proof.
  induction PS as [|[[a sh] P] PS IH]; simpl; intros Hin HF; [contradiction|].
  inv HF. unfold peers_rep in *; simpl. destruct Hin as [<- | Hin].
  - apply sepcon_valid_pointer1. apply hc4b_hs_zf_vp_peer_rep; auto.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hc4b_hs_zf_vp_dev2 sh wg D x :
  readable_share sh -> In x [wg; id_addr wg; cc_addr wg] -> device_rep sh wg D |-- valid_pointer x.
Proof.
  intros RS Hin. unfold device_rep, identity_rep, checker_rep. Intros.
  destruct Hin as [<- | [<- | [<- | []]]].
  - do 4 apply sepcon_valid_pointer1.
    apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
  - do 3 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. Intros lk.
    apply data_at_valid_ptr; [auto | simpl; lia].
  - do 2 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. Intros lk.
    apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4b_hs_zf_vp_vobj CSw o x :
  In x (vobj_addrs o) -> vobj_ok o -> vobj_rep CSw o |-- valid_pointer x.
Proof.
  intros Hin OK. destruct o; simpl in Hin, OK |- *.
  - destruct Hin as [<- | []]. apply hc4b_hs_zf_vp_peer_rep; auto.
  - apply hc4b_hs_zf_vp_peers; auto.
  - apply hc4b_hs_zf_vp_dev2; auto.
  - apply hc4b_hs_zf_vp_itab; auto. destruct Hin; auto.
  - contradiction.
  - contradiction.
  - destruct Hin as [<- | []]. destruct OK as [RS LZ]. unfold bytes_at.
    apply data_at_valid_ptr; [auto | simpl; rewrite Z.max_r by lia; lia].
  - destruct Hin as [<- | []]. destruct OK as [RS LZ]. apply memory_block_valid_ptr; [auto | lia].
  - destruct Hin as [<- | []]. apply malloc_token_valid_pointer. apply (OK CSw).
Qed.

Lemma hc4b_hs_zf_vp_vobjs CSw VO x :
  In x (vobjs_addrs VO) -> Forall vobj_ok VO -> vobjs CSw VO |-- valid_pointer x.
Proof.
  induction VO as [|o VO IH]; unfold vobjs_addrs, vobjs; simpl; intros Hin HF; [contradiction|].
  inv HF. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - apply sepcon_valid_pointer1. apply hc4b_hs_zf_vp_vobj; auto.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hc4b_hs_zf_vp_all CSw whole shp p P sht tab T VO x :
  readable_share shp -> Forall vobj_ok VO -> vp_ok (hs_own p T VO) x ->
  itable sht tab T * hc4b_hs_zf_rest whole shp p P * vobjs CSw VO * TT |-- valid_pointer x.
Proof.
  intros RS VOK [-> | Hin]; [apply valid_pointer_null|].
  apply sepcon_valid_pointer1.
  unfold hs_own in Hin. destruct Hin as [<- | Hin].
  - apply sepcon_valid_pointer1, sepcon_valid_pointer2. apply hc4b_hs_zf_rest_vp; auto.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + do 2 apply sepcon_valid_pointer1. rewrite <- (sepcon_emp (itable sht tab T)).
      apply hc4b_hs_zf_vp_tab. auto.
    + apply sepcon_valid_pointer2. apply hc4b_hs_zf_vp_vobjs; auto.
Qed.

Lemma hc4b_hs_zf_vpn x : valid_pointer x |-- !! is_pointer_or_null x.
Proof. constructor. apply valid_pointer_is_pointer_or_null. Qed.

Ltac hc4b_hs_zf_pn L :=
  go_lower; match type of L with _ |-- valid_pointer ?x =>
    apply derives_trans with (valid_pointer x); [| apply hc4b_hs_zf_vpn] end;
  eapply derives_trans; [| apply L]; cancel.

Lemma hc4b_hs_zf_body :
  forall CSw, @semax_body [] hc4_G_hs_zeroed_from CSkh WgNoise.harness.x_keypairs.code.f_hs_zeroed_from (hs_zeroed_from4_spec CSw).
Proof.
  intros CSw. start_function.
  rename H into VOK, H0 into HIN, H1 into VP.
  destruct (hc4b_hs_zf_sfind_in _ _ HIN) as (she & E & HS).
  assert (HE: t_entry_d T (hs_addr p) = E) by (unfold t_entry_d, t_entry; rewrite HS; reflexivity).
  unfold hs_snap_cur in *. rewrite HE in *. change (hc4b_hs_zf_ise (t_entry_d T (hs_addr p)) E) in HE.
  unfold hs_ptrs_nn in VP. cbn [snap_of sn_entry sn_hs] in VP.
  rewrite Forall_forall in VP.
  assert (V1 := VP (e_peer (sn_entry sn)) ltac:(simpl; auto)). assert (V2 := VP (e_peer E) ltac:(simpl; auto)).
  assert (V3 := VP (hs_sid (sn_hs sn)) ltac:(simpl; auto)). assert (V4 := VP (hs_sid (p_hs P)) ltac:(simpl; auto)).
  clear VP.
  rewrite hc4b_hs_zf_mem_eq.
  assert_PROP (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) as FCH.
  { sep_apply hc4b_hs_zf_rest_props. entailer!. }
  destruct FCH as [FC HOK].
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (e_peer (sn_entry sn))) as PN1 by hc4b_hs_zf_pn (hc4b_hs_zf_vp_all CSw whole shp p P sht tab T VO (e_peer (sn_entry sn)) SH0 VOK V1).
  assert_PROP (is_pointer_or_null (e_peer E)) as PN2 by hc4b_hs_zf_pn (hc4b_hs_zf_vp_all CSw whole shp p P sht tab T VO (e_peer E) SH0 VOK V2).
  assert_PROP (is_pointer_or_null (hs_sid (sn_hs sn))) as PN3 by hc4b_hs_zf_pn (hc4b_hs_zf_vp_all CSw whole shp p P sht tab T VO (hs_sid (sn_hs sn)) SH0 VOK V3).
  assert_PROP (is_pointer_or_null (hs_sid (p_hs P))) as PN4 by hc4b_hs_zf_pn (hc4b_hs_zf_vp_all CSw whole shp p P sht tab T VO (hs_sid (p_hs P)) SH0 VOK V4).
  assert_PROP (@field_compatible CSkh t_hsnap [] s /\ hs_ok (sn_hs sn)) as FCS.
  { erewrite (@data_at_change_composite HCS CSkh _ shs t_hsnap _ _ (JMeq_refl _)) by reflexivity.
    entailer!.
    match goal with Hv: value_fits t_hsnap _ |- _ => unfold t_hsnap, hsnap_val in Hv; simplify_value_fits in Hv;
      destruct Hv as (_ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _) end.
    simplify_value_fits in A1. simplify_value_fits in A2. simplify_value_fits in A3. simplify_value_fits in A4.
    simplify_value_fits in A5. simplify_value_fits in A6. simplify_value_fits in A7. simplify_value_fits in A8.
    unfold hs_ok, bytes in *. rewrite !Zlength_map in *. tauto. }
  destruct FCS as [FCs SOK].
  pose proof (hc4b_hs_zf_fch p FC) as FCh.
  rewrite (hc4b_hs_zf_open sht tab T p she E FC W HS).
  unfold hc4b_hs_zf_hsf.
  unfold hsnap_val. rewrite hc4b_hs_zf_snap_eq.
  pose proof SOK as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  rewrite (hc4b_hs_zf_hbytes shs 32 (hs_eph (sn_hs sn))), (hc4b_hs_zf_hbytes shs 32 (hs_rstatic (sn_hs sn))),
    (hc4b_hs_zf_hbytes shs 32 (hs_reph (sn_hs sn))), (hc4b_hs_zf_hbytes shs 32 (hs_ss (sn_hs sn))),
    (hc4b_hs_zf_hbytes shs 32 (hs_psk (sn_hs sn))), (hc4b_hs_zf_hbytes shs 32 (hs_hash (sn_hs sn))),
    (hc4b_hs_zf_hbytes shs 32 (hs_ck (sn_hs sn))), (hc4b_hs_zf_hbytes shs 12 (hs_ts (sn_hs sn))) by auto.
  repeat flatten_sepcon_in_SEP.
  unfold entry_val.
  assert (Pp: isptr p) by (destruct FC; auto).
  assert (WS: writable_share she).
  { destruct W as (_ & _ & _ & HF). apply hc4b_hs_zf_sfind_In in HS.
    rewrite Forall_forall in HF. apply (HF _ HS). }
  assert (RS: readable_share she) by auto.
  pose proof HOK as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  forward.
  forward_if (temp FK._t'1 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0)))).
  { forward. forward.
    entailer!. unfold HS_ZEROED. rewrite H. rewrite Int.eq_true. cbn [andb].
    change Int.zero with (Int.repr 0). destruct (Int.eq (hs_rindex (p_hs P)) (Int.repr 0)); reflexivity. }
  { forward. entailer!. unfold HS_ZEROED. rewrite Int.eq_false by auto. reflexivity. }
  forward_if (temp FK._t'2 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P))))).
  { forward_call (shp, @field_address CSkh t_hs (DOT FH._ephemeral_private) (hs_addr p), hs_eph (p_hs P)).
    all: try solve [destruct FCh; auto | destruct FCs; auto | split; [destruct FCs | destruct FCh]; auto].
    { entailer!. simpl. rewrite N1. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'4 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P))))).
  { forward_call (shp, @field_address CSkh t_hs (DOT FH._remote_ephemeral) (hs_addr p), hs_reph (p_hs P)).
    all: try solve [destruct FCh; auto | destruct FCs; auto | split; [destruct FCs | destruct FCh]; auto].
    { entailer!. simpl. rewrite N3. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'6 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P))))).
  { forward_call (shp, @field_address CSkh t_hs (DOT FH._hash) (hs_addr p), hs_hash (p_hs P)).
    all: try solve [destruct FCh; auto | destruct FCs; auto | split; [destruct FCs | destruct FCh]; auto].
    { entailer!. simpl. rewrite N6. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'8 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P))))).
  { forward_call (shp, @field_address CSkh t_hs (DOT FH._chaining_key) (hs_addr p), hs_ck (p_hs P)).
    all: try solve [destruct FCh; auto | destruct FCs; auto | split; [destruct FCs | destruct FCh]; auto].
    { entailer!. simpl. rewrite N7. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'10 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false)))).
  { forward. forward. forward.
    { entailer!. apply denote_tc_test_eq_split;
      (eapply derives_trans; [| eapply (hc4b_hs_zf_vp_all CSw whole shp p P sht tab T VO); eauto]);
      rewrite (hc4b_hs_zf_open sht tab T p she E FC W HS); unfold entry_val; cancel. }
    entailer!. rewrite hc4b_hs_zf_cmp by auto. try unfold eq_dec in *.
    match goal with H: typed_true tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc4b_hs_zf_tt _ H) end.
    cbn [andb]. match goal with |- context [EqDec_val ?a ?b] => destruct (EqDec_val a b) end; reflexivity. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'11 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) && Int.eq (e_type (sn_entry sn)) (e_type E)))).
  { forward. forward. forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'12 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P))))).
  { forward. forward. forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'13 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && (if eq_dec (hs_sid (sn_hs sn)) (hs_sid (p_hs P)) then true else false)))).
  { forward. forward. forward.
    { entailer!. apply denote_tc_test_eq_split;
      (eapply derives_trans; [| eapply (hc4b_hs_zf_vp_all CSw whole shp p P sht tab T VO); eauto]);
      rewrite (hc4b_hs_zf_open sht tab T p she E FC W HS); unfold entry_val; cancel. }
    entailer!. rewrite hc4b_hs_zf_cmp by auto. try unfold eq_dec in *.
    match goal with H: typed_true tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc4b_hs_zf_tt _ H) end.
    cbn [andb]. match goal with |- context [EqDec_val ?a ?b] => destruct (EqDec_val a b) end; reflexivity. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'14 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && (if eq_dec (hs_sid (sn_hs sn)) (hs_sid (p_hs P)) then true else false) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._remote_static) s, hs_rstatic (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._remote_static) (hs_addr p), hs_rstatic (p_hs P)).
    all: try solve [destruct FCh; auto | destruct FCs; auto | split; [destruct FCs | destruct FCh]; auto].
    { entailer!. simpl. rewrite M2. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'16 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && (if eq_dec (hs_sid (sn_hs sn)) (hs_sid (p_hs P)) then true else false) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._precomputed_static_static) s, hs_ss (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._precomputed_static_static) (hs_addr p), hs_ss (p_hs P)).
    all: try solve [destruct FCh; auto | destruct FCs; auto | split; [destruct FCs | destruct FCh]; auto].
    { entailer!. simpl. rewrite M4. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'18 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && (if eq_dec (hs_sid (sn_hs sn)) (hs_sid (p_hs P)) then true else false) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._preshared_key) s, hs_psk (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._preshared_key) (hs_addr p), hs_psk (p_hs P)).
    all: try solve [destruct FCh; auto | destruct FCs; auto | split; [destruct FCs | destruct FCh]; auto].
    { entailer!. simpl. rewrite M5. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward_if (temp FK._t'20 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && (if eq_dec (e_peer (sn_entry sn)) (e_peer E) then true else false) && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && (if eq_dec (hs_sid (sn_hs sn)) (hs_sid (p_hs P)) then true else false) && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P)) && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts (p_hs P))))).
  { forward_call (shs, @field_address CSkh t_hsnap (DOT FH._latest_timestamp) s, hs_ts (sn_hs sn),
                  shp, @field_address CSkh t_hs (DOT FH._latest_timestamp) (hs_addr p), hs_ts (p_hs P)).
    all: try solve [destruct FCh; auto | destruct FCs; auto | split; [destruct FCs | destruct FCh]; auto].
    { entailer!. simpl. rewrite M8. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc4b_hs_zf_fin. }
  { forward. hc4b_hs_zf_fin_false. }
  forward.
  unfold hsnap_val. rewrite hc4b_hs_zf_snap_eq.
  rewrite (hc4b_hs_zf_hbytes shs 32 (hs_eph (sn_hs sn))), (hc4b_hs_zf_hbytes shs 32 (hs_rstatic (sn_hs sn))),
    (hc4b_hs_zf_hbytes shs 32 (hs_reph (sn_hs sn))), (hc4b_hs_zf_hbytes shs 32 (hs_ss (sn_hs sn))),
    (hc4b_hs_zf_hbytes shs 32 (hs_psk (sn_hs sn))), (hc4b_hs_zf_hbytes shs 32 (hs_hash (sn_hs sn))),
    (hc4b_hs_zf_hbytes shs 32 (hs_ck (sn_hs sn))), (hc4b_hs_zf_hbytes shs 12 (hs_ts (sn_hs sn))) by auto.
  rewrite hc4b_hs_zf_mem_eq. unfold hc4b_hs_zf_hsf.
  rewrite (hc4b_hs_zf_open sht tab T p she E FC W HS). unfold entry_val.
  try unfold hs_snap_cur. unfold hc4b_hs_zf_ise in HE. rewrite HE.
  entailer!.
  unfold zeroed_from, snap_of. cbn [sn_entry sn_hs]. change Int.zero with (Int.repr 0). try unfold eq_dec in *.
  match goal with |- context [Val.of_bool ?X] => destruct X; reflexivity end.
Qed.
