(* hc_pieces3, group snap, hs_zeroed_from alone: common.h bodies, proved once at a small compspecs with the callee context
   of hc3_ctx.v.  One lemma per function (per law where the Clight
   reads a renamed constant). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

(* ---- helpers of hs_zeroed_from ---- *)
#[local] Existing Instance CSkh.
#[local] Instance hc3b_snap_zf_i1 : change_composite_env HCS CSkh. make_cs_preserve HCS CSkh. Defined.
#[local] Instance hc3b_snap_zf_i2 : change_composite_env CSkh HCS. make_cs_preserve CSkh HCS. Defined.
#[local] Instance hc3b_snap_zf_i3 : change_composite_env Noise.CS CSkh. make_cs_preserve Noise.CS CSkh. Defined.
#[local] Instance hc3b_snap_zf_i4 : change_composite_env CSkh Noise.CS. make_cs_preserve CSkh Noise.CS. Defined.

Lemma hc3b_snap_zf_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
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
Definition hc3b_snap_zf_ths := Tstruct FH._noise_handshake noattr.

Lemma hc3b_snap_zf_snap_eq shs (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
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

Lemma hc3b_snap_zf_hbytes sh n A x :
  Zlength A = n -> @data_at CSkh sh (tarray tuchar n) (bytes A) x = hbytes sh A x.
Proof. intros <-. unfold hbytes. apply hc3b_snap_zf_data_at_cs. Qed.

Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.

Lemma hc3b_snap_zf_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hc3b_snap_zf_sfind_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma hc3b_snap_zf_sfind_In (D: list (val * share * entry)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Definition hc3b_snap_zf_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Definition hc3b_snap_zf_hsf (sh: share) (h: val) (H: handshake) : mpred :=
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

Local Ltac hc3b_snap_zf_cc f v :=
  rewrite (@field_at_change_composite Noise.CS CSkh _ _ t_hs (DOT f) v v (JMeq_refl v)) by reflexivity.

Lemma hc3b_snap_zf_hsf_eq sh h H :
  hs_ok H ->
  hc3b_snap_zf_hsf sh h H =
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
  unfold hc3b_snap_zf_hsf.
  hc3b_snap_zf_cc I._state (Vint (hs_state H)).
  hc3b_snap_zf_cc I._last_initiation_consumption (Vlong (hs_lic H)).
  hc3b_snap_zf_cc I._static_identity (hs_sid H). hc3b_snap_zf_cc I._remote_index (Vint (hs_rindex H)).
  hc3b_snap_zf_cc I._ephemeral_private (bytes (hs_eph H)).
  hc3b_snap_zf_cc I._remote_static (bytes (hs_rstatic H)).
  hc3b_snap_zf_cc I._remote_ephemeral (bytes (hs_reph H)).
  hc3b_snap_zf_cc I._precomputed_static_static (bytes (hs_ss H)).
  hc3b_snap_zf_cc I._preshared_key (bytes (hs_psk H)). hc3b_snap_zf_cc I._hash (bytes (hs_hash H)).
  hc3b_snap_zf_cc I._chaining_key (bytes (hs_ck H)). hc3b_snap_zf_cc I._latest_timestamp (bytes (hs_ts H)).
  rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
    (field_at_data_at sh t_hs (DOT I._remote_static)),
    (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
    (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
    (field_at_data_at sh t_hs (DOT I._preshared_key)),
    (field_at_data_at sh t_hs (DOT I._hash)),
    (field_at_data_at sh t_hs (DOT I._chaining_key)),
    (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
  simpl nested_field_type.
  rewrite (hc3b_snap_zf_hbytes sh 32 (hs_eph H)), (hc3b_snap_zf_hbytes sh 32 (hs_rstatic H)),
    (hc3b_snap_zf_hbytes sh 32 (hs_reph H)), (hc3b_snap_zf_hbytes sh 32 (hs_ss H)),
    (hc3b_snap_zf_hbytes sh 32 (hs_psk H)), (hc3b_snap_zf_hbytes sh 32 (hs_hash H)),
    (hc3b_snap_zf_hbytes sh 32 (hs_ck H)), (hc3b_snap_zf_hbytes sh 12 (hs_ts H)) by auto.
  reflexivity.
Qed.

Lemma hc3b_snap_zf_peer_eq sh p P :
  peer_rep sh p P = hc3b_snap_zf_hsf sh (hs_addr p) (p_hs P) * hc3b_snap_zf_prest sh p P.
Proof.
  unfold peer_rep, hs_rep, hc3b_snap_zf_prest.
  apply pred_ext.
  - Intros. rewrite hc3b_snap_zf_hsf_eq by auto. Intros lk. Exists lk. entailer!.
  - Intros lk. rewrite hc3b_snap_zf_hsf_eq by auto. entailer!. Exists lk. cancel.
Qed.

Lemma hc3b_snap_zf_fc p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_peer [] p.
Proof. intros. apply (@field_compatible_change_composite Noise.CS CSkh _ t_peer); auto. Qed.

Lemma hc3b_snap_zf_entry_fa sh v p :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at CSkh sh t_hs (DOT FH._entry) v (hs_addr p).
Proof.
  intros FC0. pose proof (hc3b_snap_zf_fc p FC0) as FC.
  rewrite (@data_at_change_composite Noise.CS CSkh _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: field_compatible t_hs (DOT FH._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hc3b_snap_zf_open sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
  (@field_at CSkh she t_hs (DOT FH._entry) (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p) *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (hc3b_snap_zf_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hc3b_snap_zf_entry_fa by auto.
  apply pred_ext; entailer!.
Qed.

Lemma hc3b_snap_zf_pool_ptrs L (D: list (val * share * entry)) :
  iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [|[[x sh] e] D IH]; simpl.
  - entailer!.
  - assert_PROP (Forall isptr (saddrs D)) as HF by (sep_apply IH; entailer!).
    unfold pool_item_rep at 1, entry_at.
    assert_PROP (isptr x) as Hx by (entailer!; match goal with Hc: field_compatible _ _ x |- _ => destruct Hc; auto end).
    entailer!.
Qed.

Lemma hc3b_snap_zf_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

Lemma hc3b_snap_zf_succ_in T a :
  itable_wf T -> succ_in (t_L T) a = nullval \/ In (succ_in (t_L T) a) (saddrs (t_D T)).
Proof.
  intros (_ & HI & _). destruct (hc3b_snap_zf_succ (t_L T) a) as [-> | Hin]; auto.
Qed.

Lemma hc3b_snap_zf_ptr_or_null T x :
  Forall isptr (saddrs (t_D T)) -> x = nullval \/ In x (saddrs (t_D T)) -> is_pointer_or_null x.
Proof.
  intros HF [-> | Hin]; [simpl; auto|].
  rewrite Forall_forall in HF. apply HF in Hin. destruct x; try contradiction; exact I.
Qed.

Lemma hc3b_snap_zf_fch p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_hs [] (hs_addr p).
Proof.
  intros FC0. pose proof (hc3b_snap_zf_fc p FC0) as FC.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

(* valid pointers for the comparisons *)
Lemma hc3b_snap_zf_vp_tab sht tab T x R :
  x = nullval \/ In x (saddrs (t_D T)) -> itable sht tab T * R |-- valid_pointer x.
Proof.
  intros [-> | Ha]; [apply valid_pointer_null|].
  apply sepcon_valid_pointer1.
  destruct (hc3b_snap_zf_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (hc3b_snap_zf_split _ _ _ _ _ HE).
  assert (writable_share sh).
  { destruct H as (_ & _ & _ & HF). apply hc3b_snap_zf_sfind_In in HE.
    rewrite Forall_forall in HF. apply (HF _ HE). }
  unfold pool_item_rep, entry_at.
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc3b_snap_zf_vp_peer sh p P R :
  readable_share sh -> hc3b_snap_zf_prest sh p P * R |-- valid_pointer p.
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold hc3b_snap_zf_prest. Intros.
  do 12 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hc3b_snap_zf_vp_dev sh wg D R :
  readable_share sh -> device_rep sh wg D * R |-- valid_pointer (id_addr wg).
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold device_rep, identity_rep. Intros.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply sepcon_valid_pointer2. Intros lk.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

(* a pointer comparison (both pointers or NULL) as the model's eq_dec *)
Lemma hc3b_snap_zf_cmp x y : is_pointer_or_null x -> is_pointer_or_null y ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y))) =
  Val.of_bool (if eq_dec x y then true else false).
Proof.
  intros Hx Hy.
  destruct x; try contradiction; destruct y; try contradiction; simpl in Hx, Hy; subst;
  destruct (eq_dec _ _) as [Heq|Hne]; unfold sem_cmp_pp; simpl; try congruence; try reflexivity.
  - destruct (eq_block b b0); [|congruence]. subst. inv Heq. rewrite Ptrofs.eq_true. reflexivity.
  - destruct (eq_block b b0); [|reflexivity]. subst. rewrite Ptrofs.eq_false by congruence. reflexivity.
Qed.

Definition hc3b_snap_zf_is (a b: val) : Prop := a = b.
Definition hc3b_snap_zf_isb (a b: bool) : Prop := a = b.

Lemma hc3b_snap_zf_tt (b: bool) : typed_true tint (if b then Vtrue else Vfalse) -> b = true.
Proof. destruct b; auto. intros X. inv X. Qed.
Lemma hc3b_snap_zf_tf (b: bool) : typed_false tint (if b then Vtrue else Vfalse) -> b = false.
Proof. destruct b; auto. intros X. inv X. Qed.

Lemma hc3b_snap_zf_ofb (b: bool) :
  Val.of_bool b = Vint (if Int.eq (if b then Int.one else Int.zero) Int.zero then Int.zero else Int.one).
Proof. destruct b; reflexivity. Qed.

Ltac hc3b_snap_zf_fin :=
  entailer!;
  match goal with H: typed_true tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc3b_snap_zf_tt _ H) end;
  cbn [andb];
  first [apply hc3b_snap_zf_ofb | idtac];
  repeat match goal with |- context [Bool.eqb ?x ?y] => destruct x; destruct y end;
  simpl; unfold Val.of_bool;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Ltac hc3b_snap_zf_fin_false :=
  entailer!;
  match goal with H: typed_false tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc3b_snap_zf_tf _ H) end;
  reflexivity.

Lemma hc3b_snap_zf_eqb sn T p E H wg :
  e_peer (sn_entry sn) = p -> e_peer E = p -> hs_sid (sn_hs sn) = id_addr wg -> hs_sid H = id_addr wg ->
  zeroed_from sn (snap_of T (hs_addr p) E H) =
  (Int.eq (hs_state H) HS_ZEROED && Int.eq (hs_rindex H) (Int.repr 0) && is_zero (hs_eph H) && is_zero (hs_reph H) && is_zero (hs_hash H) && is_zero (hs_ck H) && true && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic H) && true && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic H) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss H) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk H) && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts H))%bool.
Proof.
  intros E1 E2 E3 E4.
  unfold zeroed_from, snap_of. cbn [sn_entry sn_next sn_hashed sn_hs].
  rewrite E1, E2, E3, E4. destruct (eq_dec p p); [|congruence].
  destruct (eq_dec (id_addr wg) (id_addr wg)); [|congruence]. reflexivity.
Qed.

Lemma hc3b_snap_zf_body :
  @semax_body [] (hc3_G_hs_zeroed_from) CSkh FH.f_hs_zeroed_from (hs_zeroed_from_spec).
Proof.
  start_function.
  destruct H as (HE & EP & SP & SS & PS & SN).
  assert_PROP (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) as FCH.
  { rewrite hc3b_snap_zf_peer_eq. unfold hc3b_snap_zf_prest. entailer!. }
  destruct FCH as [FC HOK].
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  unfold t_entry in HE. destruct (sfind (t_D T) (hs_addr p)) as [[she E']|] eqn:HS; [|discriminate].
  injection HE as HE. subst E'.
  assert_PROP (field_compatible t_hsnap [] s /\ hs_ok (sn_hs sn)) as FCS.
  { erewrite (@data_at_change_composite HCS CSkh _ shs t_hsnap _ _ (JMeq_refl _)) by reflexivity.
    entailer!.
    match goal with Hv: value_fits t_hsnap _ |- _ => unfold t_hsnap, hsnap_val in Hv; simplify_value_fits in Hv;
      destruct Hv as (_ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _) end.
    simplify_value_fits in A1. simplify_value_fits in A2. simplify_value_fits in A3. simplify_value_fits in A4.
    simplify_value_fits in A5. simplify_value_fits in A6. simplify_value_fits in A7. simplify_value_fits in A8.
    unfold hs_ok, bytes in *. rewrite !Zlength_map in *. tauto. }
  destruct FCS as [FCs SOK].
  pose proof (hc3b_snap_zf_fch p FC) as FCh.
  assert_PROP (isptr wg) as Pwg.
  { unfold device_rep. entailer!. match goal with Hc: field_compatible _ _ wg |- _ => destruct Hc; auto end. }
  rewrite (hc3b_snap_zf_open sht tab T p she E FC W HS).
  rewrite hc3b_snap_zf_peer_eq. unfold hc3b_snap_zf_hsf.
  unfold hsnap_val. rewrite hc3b_snap_zf_snap_eq.
  pose proof SOK as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  rewrite (hc3b_snap_zf_hbytes shs 32 (hs_eph (sn_hs sn))), (hc3b_snap_zf_hbytes shs 32 (hs_rstatic (sn_hs sn))),
    (hc3b_snap_zf_hbytes shs 32 (hs_reph (sn_hs sn))), (hc3b_snap_zf_hbytes shs 32 (hs_ss (sn_hs sn))),
    (hc3b_snap_zf_hbytes shs 32 (hs_psk (sn_hs sn))), (hc3b_snap_zf_hbytes shs 32 (hs_hash (sn_hs sn))),
    (hc3b_snap_zf_hbytes shs 32 (hs_ck (sn_hs sn))), (hc3b_snap_zf_hbytes shs 12 (hs_ts (sn_hs sn))) by auto.
  repeat flatten_sepcon_in_SEP.
  unfold entry_val.
  rewrite SP, SS, PS.
  change (hc3b_snap_zf_is (e_peer E) p) in EP. change (hc3b_snap_zf_is (e_peer (sn_entry sn)) p) in SP.
  assert (Pp: isptr p) by (destruct FC; auto).
  assert (WS: writable_share she).
  { destruct W as (_ & _ & _ & HF). apply hc3b_snap_zf_sfind_In in HS.
    rewrite Forall_forall in HF. apply (HF _ HS). }
  assert (RS: readable_share she) by auto.
  pose proof HOK as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  forward.
  forward_if (temp FH._t'1 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0)))).
  { forward. forward.
    entailer!. unfold HS_ZEROED. rewrite H. rewrite Int.eq_true. cbn [andb].
    destruct (Int.eq (hs_rindex (p_hs P)) (Int.repr 0)); reflexivity. }
  { forward. entailer!. unfold HS_ZEROED. rewrite Int.eq_false by auto. reflexivity. }
  forward_if (temp FH._t'2 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P))))).
  { forward_call (shp, field_address t_hs (DOT FH._ephemeral_private) (hs_addr p), hs_eph (p_hs P)).
    { entailer!. simpl. rewrite N1. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'4 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P))))).
  { forward_call (shp, field_address t_hs (DOT FH._remote_ephemeral) (hs_addr p), hs_reph (p_hs P)).
    { entailer!. simpl. rewrite N3. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'6 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P))))).
  { forward_call (shp, field_address t_hs (DOT FH._hash) (hs_addr p), hs_hash (p_hs P)).
    { entailer!. simpl. rewrite N6. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'8 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P))))).
  { forward_call (shp, field_address t_hs (DOT FH._chaining_key) (hs_addr p), hs_ck (p_hs P)).
    { entailer!. simpl. rewrite N7. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'10 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && true))).
  { forward. forward. forward.
    { entailer!. unfold hc3b_snap_zf_is in EP; rewrite EP; apply denote_tc_test_eq_split;
      (apply (derives_trans _ (hc3b_snap_zf_prest shp p P * TT)); [cancel | apply hc3b_snap_zf_vp_peer; auto]). }
    entailer!. unfold hc3b_snap_zf_is in EP; rewrite EP.
    rewrite hc3b_snap_zf_cmp by (destruct p; try contradiction; exact I).
    match goal with H: typed_true tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc3b_snap_zf_tt _ H) end.
    destruct (eq_dec p p); [reflexivity | congruence]. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'11 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && true && Int.eq (e_type (sn_entry sn)) (e_type E)))).
  { forward. forward. forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'12 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && true && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P))))).
  { forward. forward. forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'13 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && true && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && true))).
  { forward.
    { entailer!. unfold id_addr; destruct wg; try contradiction; exact I. }
    forward. forward.
    { entailer!. apply denote_tc_test_eq_split;
      (apply (derives_trans _ (device_rep shd wg D * TT)); [cancel | apply hc3b_snap_zf_vp_dev; auto]). }
    entailer!. rewrite hc3b_snap_zf_cmp by (unfold id_addr; destruct wg; try contradiction; exact I).
    match goal with H: typed_true tint (if ?b then Vtrue else Vfalse) |- _ => rewrite (hc3b_snap_zf_tt _ H) end.
    destruct (eq_dec (id_addr wg) (id_addr wg)); [reflexivity | congruence]. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'14 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && true && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && true && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._remote_static) s, hs_rstatic (sn_hs sn),
                  shp, field_address t_hs (DOT FH._remote_static) (hs_addr p), hs_rstatic (p_hs P)).
    { entailer!. simpl. rewrite M2. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'16 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && true && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && true && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._precomputed_static_static) s, hs_ss (sn_hs sn),
                  shp, field_address t_hs (DOT FH._precomputed_static_static) (hs_addr p), hs_ss (p_hs P)).
    { entailer!. simpl. rewrite M4. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'18 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && true && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && true && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._preshared_key) s, hs_psk (sn_hs sn),
                  shp, field_address t_hs (DOT FH._preshared_key) (hs_addr p), hs_psk (p_hs P)).
    { entailer!. simpl. rewrite M5. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward_if (temp FH._t'20 (Val.of_bool (Int.eq (hs_state (p_hs P)) HS_ZEROED && Int.eq (hs_rindex (p_hs P)) (Int.repr 0) && is_zero (hs_eph (p_hs P)) && is_zero (hs_reph (p_hs P)) && is_zero (hs_hash (p_hs P)) && is_zero (hs_ck (p_hs P)) && true && Int.eq (e_type (sn_entry sn)) (e_type E) && Int64.eq (hs_lic (sn_hs sn)) (hs_lic (p_hs P)) && true && bytes_eqb (hs_rstatic (sn_hs sn)) (hs_rstatic (p_hs P)) && bytes_eqb (hs_ss (sn_hs sn)) (hs_ss (p_hs P)) && bytes_eqb (hs_psk (sn_hs sn)) (hs_psk (p_hs P)) && bytes_eqb (hs_ts (sn_hs sn)) (hs_ts (p_hs P))))).
  { forward_call (shs, field_address t_hsnap (DOT FH._latest_timestamp) s, hs_ts (sn_hs sn),
                  shp, field_address t_hs (DOT FH._latest_timestamp) (hs_addr p), hs_ts (p_hs P)).
    { entailer!. simpl. rewrite M8. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. hc3b_snap_zf_fin. }
  { forward. hc3b_snap_zf_fin_false. }
  forward.
  unfold hsnap_val. rewrite hc3b_snap_zf_snap_eq. rewrite SS.
  unfold hc3b_snap_zf_is in SP. rewrite SP.
  rewrite (hc3b_snap_zf_hbytes shs 32 (hs_eph (sn_hs sn))), (hc3b_snap_zf_hbytes shs 32 (hs_rstatic (sn_hs sn))),
    (hc3b_snap_zf_hbytes shs 32 (hs_reph (sn_hs sn))), (hc3b_snap_zf_hbytes shs 32 (hs_ss (sn_hs sn))),
    (hc3b_snap_zf_hbytes shs 32 (hs_psk (sn_hs sn))), (hc3b_snap_zf_hbytes shs 32 (hs_hash (sn_hs sn))),
    (hc3b_snap_zf_hbytes shs 32 (hs_ck (sn_hs sn))), (hc3b_snap_zf_hbytes shs 12 (hs_ts (sn_hs sn))) by auto.
  rewrite hc3b_snap_zf_peer_eq. unfold hc3b_snap_zf_hsf. rewrite PS.
  rewrite (hc3b_snap_zf_open sht tab T p she E FC W HS). unfold entry_val.
  unfold hc3b_snap_zf_is in EP.
  rewrite (hc3b_snap_zf_eqb sn T p E (p_hs P) wg SP EP SS PS).
  entailer!.
  match goal with |- Val.of_bool ?X = _ => destruct X; reflexivity end.
Qed.
