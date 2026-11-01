(* law consume_response_any, phase Q5, segment A4: opening QA1 into the block lemmas' state
   (hcr5_q5_A4_core.v), port of v1's hcr3_q5_A4.v.  The node is one data_at CKS in hnodes_rep4: its snap field is
   reached by gfield_ramif (as consume_initiation's hci5_p8_A3_sep.v), the other fields stay in the wand.
   "Q5 A4" (frame trick, kernel-time pitfalls). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_pure.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A4_core.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope Z_scope.

#[local] Instance hcr5_q5_A4_cce_K : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.
#[local] Instance hcr5_q5_A4_cce_N : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.

Local Open Scope logic.

Lemma hcr5_q5_A4_dcs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  assert (forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (H (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (H (@cenv_cs cs2) (Ptrofs.unsigned i)). tauto.
Qed.

Lemma hcr5_q5_A4_hb sh n A p : Zlength A = n ->
  @data_at W_consume_response_any sh (tarray tuchar n) (bytes A) p = hbytes sh A p.
Proof. intros <-. unfold hbytes. apply hcr5_q5_A4_dcs. Qed.

Lemma hcr5_q5_A4_snap_split shs (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
  @data_at W_consume_response_any shs t_hsnap
    (a, (b, (c, (d, (e, (f, (g, (h, (l1, (l2, (l3, (l4, (l5, (l6, (l7, (l8, ri)))))))))))))))) s =
  field_at shs t_hsnap (DOT HR5._peer) a s * field_at shs t_hsnap (DOT HR5._next) b s *
  field_at shs t_hsnap (DOT HR5._hashed) c s * spacer shs 17 20 s *
  field_at shs t_hsnap (DOT HR5._type) d s * field_at shs t_hsnap (DOT HR5._index) e s *
  field_at shs t_hsnap (DOT HR5._state) f s * field_at shs t_hsnap (DOT HR5._last_initiation_consumption) g s *
  field_at shs t_hsnap (DOT HR5._static_identity) h s *
  data_at shs (tarray tuchar 32) l1 (field_address t_hsnap (DOT HR5._ephemeral_private) s) *
  data_at shs (tarray tuchar 32) l2 (field_address t_hsnap (DOT HR5._remote_static) s) *
  data_at shs (tarray tuchar 32) l3 (field_address t_hsnap (DOT HR5._remote_ephemeral) s) *
  data_at shs (tarray tuchar 32) l4 (field_address t_hsnap (DOT HR5._precomputed_static_static) s) *
  data_at shs (tarray tuchar 32) l5 (field_address t_hsnap (DOT HR5._preshared_key) s) *
  data_at shs (tarray tuchar 32) l6 (field_address t_hsnap (DOT HR5._hash) s) *
  data_at shs (tarray tuchar 32) l7 (field_address t_hsnap (DOT HR5._chaining_key) s) *
  data_at shs (tarray tuchar 12) l8 (field_address t_hsnap (DOT HR5._latest_timestamp) s) *
  field_at shs t_hsnap (DOT HR5._remote_index) ri s.
Proof.
  match goal with |- @data_at _ _ _ ?v _ = _ => set (V := v) end.
  unfold data_at.
  rewrite (@field_at_Tstruct W_consume_response_any shs t_hsnap [] HR5._hs_snap noattr V V s eq_refl (JMeq_refl _)).
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at].
  simpl struct_pred. unfold withspacer. simpl nested_field_offset. simpl sizeof.
  repeat match goal with |- context [Z.eq_dec ?x ?y] =>
    destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
  subst V.
  rewrite (field_at_data_at shs t_hsnap (DOT HR5._ephemeral_private)),
    (field_at_data_at shs t_hsnap (DOT HR5._remote_static)),
    (field_at_data_at shs t_hsnap (DOT HR5._remote_ephemeral)),
    (field_at_data_at shs t_hsnap (DOT HR5._precomputed_static_static)),
    (field_at_data_at shs t_hsnap (DOT HR5._preshared_key)),
    (field_at_data_at shs t_hsnap (DOT HR5._hash)),
    (field_at_data_at shs t_hsnap (DOT HR5._chaining_key)),
    (field_at_data_at shs t_hsnap (DOT HR5._latest_timestamp)).
  simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

(* the accepted peer: the handshake fields the CHECK reads (at the world), the rest *)

Definition hcr5_q5_A4_prest2 (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  @field_at Noise.CS Ews t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  kps_rep Ews (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  @field_at Noise.CS Ews t_hs [StructField I._state] (Vint (hs_state H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._hash] (bytes (hs_hash H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
  @field_at Noise.CS Ews t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
  (EX lk: val, @field_at Noise.CS Ews t_hs [StructField I._lock] lk h) *
  spacer Ews 36 40 h * spacer Ews 300 304 h *
  @field_at Noise.CS Ews t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
  cookie_rep Ews (cookie_addr p) (p_cookie P) *
  @field_at Noise.CS Ews t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  @field_at Noise.CS Ews t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
  @field_at Noise.CS Ews t_peer [StructField I._pubkey_next] (p_pknext P) p *
  spacer Ews 9 16 p * spacer Ews 476 480 p.

Definition hcr5_q5_A4_prest (p: val) (P: peer) : mpred :=
  @field_at Noise.CS Ews t_peer [StructField I._device] (p_device P) p * hcr5_q5_A4_prest2 p P.

Definition hcr5_q5_A4_hsc (h sid: val) (lic: int64) (eph rs ss psk ts: list byte) : mpred :=
  @field_at W_consume_response_any Ews t_hs (DOT HR5._static_identity) sid h *
  @field_at W_consume_response_any Ews t_hs (DOT HR5._last_initiation_consumption) (Vlong lic) h *
  hbytes Ews eph (@field_address W_consume_response_any t_hs (DOT HR5._ephemeral_private) h) *
  hbytes Ews rs (@field_address W_consume_response_any t_hs (DOT HR5._remote_static) h) *
  hbytes Ews ss (@field_address W_consume_response_any t_hs (DOT HR5._precomputed_static_static) h) *
  hbytes Ews psk (@field_address W_consume_response_any t_hs (DOT HR5._preshared_key) h) *
  hbytes Ews ts (@field_address W_consume_response_any t_hs (DOT HR5._latest_timestamp) h).

Ltac hcr5_q5_A4_hsf_tac :=
  intros Hl; match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W_consume_response_any _ sh t gfs v v (JMeq_refl v)) by reflexivity end;
  rewrite field_at_data_at; rewrite <- (hcr5_q5_A4_hb _ _ _ _ Hl); reflexivity.

Lemma hcr5_q5_A4_f_eph sh A h : Zlength A = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._ephemeral_private) (bytes A) h =
  hbytes sh A (@field_address W_consume_response_any t_hs (DOT HR5._ephemeral_private) h).
Proof. hcr5_q5_A4_hsf_tac. Qed.
Lemma hcr5_q5_A4_f_rs sh A h : Zlength A = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._remote_static) (bytes A) h =
  hbytes sh A (@field_address W_consume_response_any t_hs (DOT HR5._remote_static) h).
Proof. hcr5_q5_A4_hsf_tac. Qed.
Lemma hcr5_q5_A4_f_ss sh A h : Zlength A = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._precomputed_static_static) (bytes A) h =
  hbytes sh A (@field_address W_consume_response_any t_hs (DOT HR5._precomputed_static_static) h).
Proof. hcr5_q5_A4_hsf_tac. Qed.
Lemma hcr5_q5_A4_f_psk sh A h : Zlength A = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._preshared_key) (bytes A) h =
  hbytes sh A (@field_address W_consume_response_any t_hs (DOT HR5._preshared_key) h).
Proof. hcr5_q5_A4_hsf_tac. Qed.
Lemma hcr5_q5_A4_f_ts sh A h : Zlength A = 12 ->
  @field_at Noise.CS sh t_hs (DOT I._latest_timestamp) (bytes A) h =
  hbytes sh A (@field_address W_consume_response_any t_hs (DOT HR5._latest_timestamp) h).
Proof. hcr5_q5_A4_hsf_tac. Qed.
Lemma hcr5_q5_A4_f_sid sh v h :
  @field_at Noise.CS sh t_hs (DOT I._static_identity) v h =
  @field_at W_consume_response_any sh t_hs (DOT HR5._static_identity) v h.
Proof.
  rewrite (@field_at_change_composite Noise.CS W_consume_response_any _ sh t_hs _ v v (JMeq_refl v)) by reflexivity.
  reflexivity.
Qed.
Lemma hcr5_q5_A4_f_lic sh v h :
  @field_at Noise.CS sh t_hs (DOT I._last_initiation_consumption) v h =
  @field_at W_consume_response_any sh t_hs (DOT HR5._last_initiation_consumption) v h.
Proof.
  rewrite (@field_at_change_composite Noise.CS W_consume_response_any _ sh t_hs _ v v (JMeq_refl v)) by reflexivity.
  reflexivity.
Qed.

Lemma hcr5_q5_A4_peer_eq p P :
  peer_rep Ews p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
  (hcr5_q5_A4_hsc (hs_addr p) (hs_sid (p_hs P)) (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P))
     (hs_ss (p_hs P)) (hs_psk (p_hs P)) (hs_ts (p_hs P)) * hcr5_q5_A4_prest p P).
Proof.
  unfold peer_rep, hs_rep, hcr5_q5_A4_hsc, hcr5_q5_A4_prest, hcr5_q5_A4_prest2.
  apply pred_ext.
  - Intros. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    rewrite (hcr5_q5_A4_f_eph Ews _ _ L1), (hcr5_q5_A4_f_rs Ews _ _ L2), (hcr5_q5_A4_f_ss Ews _ _ L4),
      (hcr5_q5_A4_f_psk Ews _ _ L5), (hcr5_q5_A4_f_ts Ews _ _ L8), hcr5_q5_A4_f_sid, hcr5_q5_A4_f_lic.
    Intros lk. entailer!. Exists lk. cancel.
  - Intros. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    rewrite (hcr5_q5_A4_f_eph Ews _ _ L1), (hcr5_q5_A4_f_rs Ews _ _ L2), (hcr5_q5_A4_f_ss Ews _ _ L4),
      (hcr5_q5_A4_f_psk Ews _ _ L5), (hcr5_q5_A4_f_ts Ews _ _ L8), hcr5_q5_A4_f_sid, hcr5_q5_A4_f_lic.
    Intros lk. entailer!. Exists lk. cancel.
Qed.

(* the peer at a in the list after an update *)
Lemma hcr5_q5_A4_peers PS a sh P Q : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a Q) = peer_rep sh a Q * peers_rep (sdel PS a).
Proof.
  induction PS as [| [[x sh0] w] PS IH]; simpl; intros Hf; [discriminate |].
  unfold peers_rep in *. destruct (EqDec_val x a) as [Ex | Hne]; [subst x |].
  - inversion Hf; subst. simpl. reflexivity.
  - simpl. rewrite IH by exact Hf. unfold peer_item_rep.
    rewrite <- !sepcon_assoc, (sepcon_comm (peer_rep sh0 x w)). reflexivity.
Qed.

(* the pool entry at h, as the field entry of the handshake *)
Lemma hcr5_q5_A4_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hcr5_q5_A4_sfind_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma hcr5_q5_A4_sfind_In (D: list (val * share * entry)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Lemma hcr5_q5_A4_fc p :
  @field_compatible Noise.CS t_peer [] p -> @field_compatible W_consume_response_any t_peer [] p.
Proof. intros. apply (@field_compatible_change_composite Noise.CS W_consume_response_any _ t_peer); auto. Qed.

Lemma hcr5_q5_A4_fch p :
  @field_compatible Noise.CS t_peer [] p -> @field_compatible W_consume_response_any t_hs [] (hs_addr p).
Proof.
  intros FC0. pose proof (hcr5_q5_A4_fc p FC0) as FC.
  assert (FC1: @field_compatible W_consume_response_any t_peer (DOT HR5._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

Lemma hcr5_q5_A4_entry_fa sh v p :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at W_consume_response_any sh t_hs (DOT HR5._entry) v (hs_addr p).
Proof.
  intros FC0. pose proof (hcr5_q5_A4_fch p FC0) as FC2.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC3: @field_compatible W_consume_response_any t_hs (DOT HR5._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (destruct FC2 as [Hp _]; exact Hp).
  reflexivity.
Qed.

Lemma hcr5_q5_A4_itable_eq sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
  (@field_at W_consume_response_any she t_hs (DOT HR5._entry)
     (e_peer E, (succ_in (t_L T) (hs_addr p), (Val.of_bool (vin (hs_addr p) (t_L T)), (Vint (e_type E), Vint (e_index E)))))
     (hs_addr p) *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (hcr5_q5_A4_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hcr5_q5_A4_entry_fa by auto. unfold entry_val.
  apply pred_ext; entailer!.
Qed.

(* valid pointers for the comparisons *)
Lemma hcr5_q5_A4_vp_tab sht tab T x R :
  x = nullval \/ In x (saddrs (t_D T)) -> itable sht tab T * R |-- valid_pointer x.
Proof.
  intros [-> | Ha]; [apply valid_pointer_null|].
  apply sepcon_valid_pointer1.
  destruct (hcr5_q5_A4_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (hcr5_q5_A4_split _ _ _ _ _ HE).
  assert (writable_share sh).
  { destruct H as (_ & _ & _ & HF). apply hcr5_q5_A4_sfind_In in HE.
    rewrite Forall_forall in HF. apply (HF _ HE). }
  unfold pool_item_rep, entry_at.
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hcr5_q5_A4_vp_dev sh wg D R :
  readable_share sh -> device_rep sh wg D * R |-- valid_pointer (id_addr wg).
Proof.
  intros RS. apply sepcon_valid_pointer1. unfold device_rep, identity_rep. Intros.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply sepcon_valid_pointer2. Intros lk.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hcr5_q5_A4_vp_prest p P R : hcr5_q5_A4_prest p P * R |-- valid_pointer p.
Proof.
  apply sepcon_valid_pointer1. unfold hcr5_q5_A4_prest. apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hcr5_q5_A4_pool_ptrs L (D: list (val * share * entry)) :
  iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [|[[x sh] e] D IH]; simpl.
  - entailer!.
  - assert_PROP (Forall isptr (saddrs D)) as HF by (sep_apply IH; entailer!).
    unfold pool_item_rep at 1, entry_at.
    assert_PROP (isptr x) as Hx by (entailer!; match goal with Hc: field_compatible _ _ x |- _ => destruct Hc; auto end).
    entailer!.
Qed.

Lemma hcr5_q5_A4_itable_ptrs sht tab T : itable sht tab T |-- !! Forall isptr (saddrs (t_D T)).
Proof. unfold itable. Intros. sep_apply hcr5_q5_A4_pool_ptrs. entailer!. Qed.

Lemma hcr5_q5_A4_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

Lemma hcr5_q5_A4_succ_in T a :
  itable_wf T -> succ_in (t_L T) a = nullval \/ In (succ_in (t_L T) a) (saddrs (t_D T)).
Proof.
  intros (_ & HI & _). destruct (hcr5_q5_A4_succ (t_L T) a) as [-> | Hin]; auto.
Qed.

Lemma hcr5_q5_A4_ptr_or_null T x :
  Forall isptr (saddrs (t_D T)) -> x = nullval \/ In x (saddrs (t_D T)) -> is_pointer_or_null x.
Proof.
  intros HF [-> | Hin]; [simpl; auto|].
  rewrite Forall_forall in HF. apply HF in Hin. destruct x; try contradiction; exact I.
Qed.

(* opening a predicate X = core * rest, keeping a wand to put it back *)
Lemma hcr5_q5_A4_wopen (X C R: mpred) (Pp: Prop) : X = !! Pp && (C * R) -> X |-- !! Pp && (C * (C -* X)).
Proof.
  intros HX. rewrite HX at 1. Intros. apply andp_right; [apply prop_right; auto |].
  apply sepcon_derives; [apply derives_refl |]. rewrite <- wand_sepcon_adjoint. rewrite HX.
  apply andp_right; [apply prop_right; auto |]. rewrite sepcon_comm. apply derives_refl.
Qed.

Lemma hcr5_q5_A4_hsnap_eq T hh E H :
  hsnap_val (snap_of T hh E H) =
  (e_peer E, (succ_in (t_L T) hh, (Val.of_bool (vin hh (t_L T)), (Vint (e_type E), (Vint (e_index E),
  (Vint (hs_state H), (Vlong (hs_lic H), (hs_sid H, (bytes (hs_eph H), (bytes (hs_rstatic H),
  (bytes (hs_reph H), (bytes (hs_ss H), (bytes (hs_psk H), (bytes (hs_hash H), (bytes (hs_ck H),
  (bytes (hs_ts H), Vint (hs_rindex H))))))))))))))))).
Proof. reflexivity. Qed.

(* the peer after wg_peer_put: the seven fields as P's *)
Lemma hcr5_q5_A4_peer_put a P M ck h :
  peer_rep Ews a (hcr5_q5_put P M ck h) =
  !! (@field_compatible Noise.CS t_peer [] a /\ hs_ok (p_hs (hcr5_q5_put P M ck h))) &&
  ((@field_at W_consume_response_any Ews t_hs (DOT HR5._static_identity) (hs_sid (p_hs P)) (hs_addr a) *
    @field_at W_consume_response_any Ews t_hs (DOT HR5._last_initiation_consumption) (Vlong (hs_lic (p_hs P))) (hs_addr a) *
    hbytes Ews (hs_eph (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._ephemeral_private) (hs_addr a)) *
    hbytes Ews (hs_rstatic (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._remote_static) (hs_addr a)) *
    hbytes Ews (hs_ss (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._precomputed_static_static) (hs_addr a)) *
    hbytes Ews (hs_psk (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._preshared_key) (hs_addr a)) *
    hbytes Ews (hs_ts (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._latest_timestamp) (hs_addr a))) *
   hcr5_q5_A4_prest a (hcr5_q5_put P M ck h)).
Proof. rewrite hcr5_q5_A4_peer_eq. reflexivity. Qed.

(* the snapshot in the node: its twelve fields read by the CHECK, the rest *)

(* ---- accessors P |-- Q * (Q -* P) (consume_initiation's hci5_p8_A3_sep.v) ---- *)
Definition hcr5_q5_A4_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hcr5_q5_A4_acc_refl Q : hcr5_q5_A4_acc Q Q.
Proof.
  unfold hcr5_q5_A4_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hcr5_q5_A4_acc_l Q A F : hcr5_q5_A4_acc Q A -> hcr5_q5_A4_acc Q (A * F).
Proof.
  unfold hcr5_q5_A4_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hcr5_q5_A4_acc_r Q A F : hcr5_q5_A4_acc Q A -> hcr5_q5_A4_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hcr5_q5_A4_acc_l, H. Qed.

Lemma hcr5_q5_A4_acc_prop Q (c: Prop) A : (c -> hcr5_q5_A4_acc Q A) -> hcr5_q5_A4_acc Q (!! c && A).
Proof.
  unfold hcr5_q5_A4_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcr5_q5_A4_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hcr5_q5_A4_acc Q (A x)) -> hcr5_q5_A4_acc Q (EX x, A x).
Proof.
  unfold hcr5_q5_A4_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply (exp_right x), derives_refl.
Qed.

Lemma hcr5_q5_A4_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hcr5_q5_A4_acc Q A) -> hcr5_q5_A4_acc Q A.
Proof.
  unfold hcr5_q5_A4_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hcr5_q5_A4_acc_trans Q B P : hcr5_q5_A4_acc Q B -> hcr5_q5_A4_acc B P -> hcr5_q5_A4_acc Q P.
Proof.
  unfold hcr5_q5_A4_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcr5_q5_A4_acc_wopen (X C R: mpred) (Pp: Prop) : X = !! Pp && (C * R) -> hcr5_q5_A4_acc C X.
Proof.
  intros HX. unfold hcr5_q5_A4_acc. eapply derives_trans; [exact (hcr5_q5_A4_wopen X C R Pp HX) |]. apply andp_left2, derives_refl.
Qed.

(* ---- the node (one data_at CKS in hnodes_rep4) ---- *)
Definition hcr5_q5_A4_nv (N: hnode4) (nx: val) : @reptype CKS t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hcr5_q5_A4_nodes_acc (Q: mpred) N : forall NS l, In N NS ->
  (forall nx, hcr5_q5_A4_acc Q (@data_at CKS Ews t_hnode4 (hcr5_q5_A4_nv N nx) (hn_addr N))) ->
  hcr5_q5_A4_acc Q (hnodes_rep4 W_consume_response_any l NS).
Proof.
  induction NS as [|N0 NS IH]; intros l Hin HQ; [destruct Hin|]. cbn [hnodes_rep4].
  apply hcr5_q5_A4_acc_prop; intros Hl. apply hcr5_q5_A4_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hcr5_q5_A4_acc_l, hcr5_q5_A4_acc_l, hcr5_q5_A4_acc_r. apply HQ.
  - apply hcr5_q5_A4_acc_r, IH; auto.
Qed.

(* the snap field of a node, at CKS (its value stays abstract: no reptype conversion) *)
Lemma hcr5_q5_A4_nfld_snap (pv: val) (V: @reptype CKS t_hsnap) (rv: val) (rs: @reptype CKS t_prsnap) nx t :
  hcr5_q5_A4_acc (@field_at CKS Ews t_hnode4 [StructField HR5._snap] V t)
    (@data_at CKS Ews t_hnode4 (pv, (V, (rv, (rs, nx)))) t).
Proof.
  unfold hcr5_q5_A4_acc.
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HR5._snap) _ V t);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ V). apply derives_refl.
Qed.

(* the field snap as a t_hsnap at s = offset_val 8 node, at W *)
Lemma hcr5_q5_A4_snap_at (v: @reptype CKS t_hsnap) x : @field_compatible CKS t_hnode4 [] x ->
  @field_at CKS Ews t_hnode4 [StructField HR5._snap] v x = @data_at W_consume_response_any Ews t_hsnap v (offset_val 8 x).
Proof.
  intros FC. rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible.
  change (@nested_field_offset CKS t_hnode4 [StructField HR5._snap]) with 8.
  change (@nested_field_type CKS t_hnode4 [StructField HR5._snap]) with t_hsnap.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hcr5_q5_A4_snapfc (V: @reptype CKS t_hsnap) x :
  @field_at CKS Ews t_hnode4 [StructField HR5._snap] V x |-- !! @field_compatible CKS t_hnode4 [] x.
Proof.
  assert_PROP (@field_compatible CKS t_hnode4 [StructField HR5._snap] x) as Hf by entailer!.
  apply prop_right. destruct Hf as (A1 & A2 & A3 & A4 & _). repeat split; auto.
Qed.

Lemma hcr5_q5_A4_vp_peerw a Q C R : C * (C -* peer_rep Ews a Q) * R |-- valid_pointer a.
Proof.
  eapply derives_trans; [apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl] |].
  rewrite hcr5_q5_A4_peer_eq. apply sepcon_valid_pointer1. Intros.
  apply sepcon_valid_pointer2. unfold hcr5_q5_A4_prest. apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma hcr5_q5_A4_vp_itw C sht tab T x R :
  x = nullval \/ In x (saddrs (t_D T)) -> C * (C -* itable sht tab T) * R |-- valid_pointer x.
Proof.
  intros Hx. eapply derives_trans; [apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl] |].
  apply hcr5_q5_A4_vp_tab; exact Hx.
Qed.

Lemma hcr5_q5_A4_peers_fold PS a sh P Q : sfind PS a = Some (sh, P) ->
  peer_rep sh a Q * peers_rep (sdel PS a) |-- peers_rep (supd PS a Q).
Proof. intros Hf. rewrite (hcr5_q5_A4_peers PS a sh P Q Hf). apply derives_refl. Qed.

Lemma hcr5_q5_A4_wopen2 (X D C R: mpred) : X = D * (C * R) -> X |-- C * (C -* X).
Proof.
  intros HX. rewrite HX at 1. rewrite <- sepcon_assoc, (sepcon_comm D C), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |]. rewrite <- wand_sepcon_adjoint. rewrite HX.
  cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* The cut of the main lemma: the block lemmas' frame is a wand back to    *)
(* QA1's own SEP list; opening (hcr5_q5_A4_open), valid pointers           *)
(* (hcr5_q5_A4_hv) and the props are separate lemmas (kernel time)         *)
(* ---------------------------------------------------------------------- *)

(* the twenty fields the CHECK reads (hcr5_q5_A4_S without its frame): the pool entry, the peer's seven
   handshake fields, the snapshot's twelve fields *)
Definition hcr5_q5_A4_Ce (hv: val) (she: share) (pe nxt: val) (hb: bool) (ty ix: int) : list mpred :=
  [@field_at W_consume_response_any she t_hs (DOT HR5._entry) (pe, (nxt, (Val.of_bool hb, (Vint ty, Vint ix)))) hv].
Definition hcr5_q5_A4_Cp (hv sid: val) (lic: int64) (eph rs ss psk ts: list byte) : list mpred :=
  [@field_at W_consume_response_any Ews t_hs (DOT HR5._static_identity) sid hv;
   @field_at W_consume_response_any Ews t_hs (DOT HR5._last_initiation_consumption) (Vlong lic) hv;
   hbytes Ews eph (@field_address W_consume_response_any t_hs (DOT HR5._ephemeral_private) hv);
   hbytes Ews rs (@field_address W_consume_response_any t_hs (DOT HR5._remote_static) hv);
   hbytes Ews ss (@field_address W_consume_response_any t_hs (DOT HR5._precomputed_static_static) hv);
   hbytes Ews psk (@field_address W_consume_response_any t_hs (DOT HR5._preshared_key) hv);
   hbytes Ews ts (@field_address W_consume_response_any t_hs (DOT HR5._latest_timestamp) hv)].
Definition hcr5_q5_A4_Cs (sv pe nxt: val) (hb: bool) (ty ix: int) (sid: val) (lic: int64)
  (eph rs ss psk ts: list byte) : list mpred :=
  [@field_at W_consume_response_any Ews t_hsnap (DOT HR5._peer) pe sv;
   @field_at W_consume_response_any Ews t_hsnap (DOT HR5._next) nxt sv;
   @field_at W_consume_response_any Ews t_hsnap (DOT HR5._hashed) (Val.of_bool hb) sv;
   @field_at W_consume_response_any Ews t_hsnap (DOT HR5._type) (Vint ty) sv;
   @field_at W_consume_response_any Ews t_hsnap (DOT HR5._index) (Vint ix) sv;
   @field_at W_consume_response_any Ews t_hsnap (DOT HR5._static_identity) sid sv;
   @field_at W_consume_response_any Ews t_hsnap (DOT HR5._last_initiation_consumption) (Vlong lic) sv;
   hbytes Ews eph (@field_address W_consume_response_any t_hsnap (DOT HR5._ephemeral_private) sv);
   hbytes Ews rs (@field_address W_consume_response_any t_hsnap (DOT HR5._remote_static) sv);
   hbytes Ews ss (@field_address W_consume_response_any t_hsnap (DOT HR5._precomputed_static_static) sv);
   hbytes Ews psk (@field_address W_consume_response_any t_hsnap (DOT HR5._preshared_key) sv);
   hbytes Ews ts (@field_address W_consume_response_any t_hsnap (DOT HR5._latest_timestamp) sv)].
Definition hcr5_q5_A4_C (hv sv: val) (she: share) (pe nxt: val) (hb: bool) (ty ix: int) (sid: val)
  (lic: int64) (eph rs ss psk ts: list byte) : list mpred :=
  hcr5_q5_A4_Ce hv she pe nxt hb ty ix ++ hcr5_q5_A4_Cp hv sid lic eph rs ss psk ts ++
  hcr5_q5_A4_Cs sv pe nxt hb ty ix sid lic eph rs ss psk ts.

Lemma hcr5_q5_A4_S_eq hv sv she pe nxt hb ty ix sid lic eph rs ss psk ts F :
  hcr5_q5_A4_S hv sv she pe nxt hb ty ix sid lic eph rs ss psk ts F =
  hcr5_q5_A4_C hv sv she pe nxt hb ty ix sid lic eph rs ss psk ts ++ [F].
Proof. reflexivity. Qed.

(* the SEP list of QA1, and the same regrouped: the itable, the node list, the peers, the rest *)

(* the SEP list of QA1, and the same regrouped: the itable, the node list, the peers, the rest *)
Definition hcr5_q5_A4_QL (x25519: list byte -> list byte -> list byte) (gv: globals) (L: hcr5_loc)
  (FR: mpred) (R: hcr5_run) (S: shim) (NS: list hnode4) (PS: list (val * share * peer)) (head: val)
  (T: tstate) (KE: list kent4) (m: val) (M: resp_msg) (a: val) (P: peer) (ck h: list byte) : list mpred :=
  hcr5_world x25519 R L NS (hnodes_snapped4 T NS PS) head T ++
  [peers_rep (supd PS a (hcr5_q5_put P M ck h));
   hbytes Tsh (resp_bytes M) (l_img L); kents_rep W_consume_response_any (hcr5_khead KE) (map (kent_snapped T) KE);
   hcr5_tok t_resp m; resp_rep Ews m M;
   @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st L); hbytes Tsh (resp_bytes M) (l_imga L)] ++
  hcr5_globs gv S FR ++ hcr5_snaps L (hcr5_DAL x25519 R L) head S ++ hcr5_q5_scr L.

Definition hcr5_q5_A4_QR (x25519: list byte -> list byte -> list byte) (gv: globals) (L: hcr5_loc)
  (FR: mpred) (R: hcr5_run) (S: shim) (NS: list hnode4) (head: val) (KE: list kent4) (T: tstate)
  (m: val) (M: resp_msg) (ck h: list byte) : list mpred :=
  [device_rep Tsh (l_wa L) (hcr5_DAL x25519 R L); ptable Tsh (l_pta L) head;
   @data_at HCS Tsh t_mident (mident_val (hcr5_IA x25519 R)) (l_ia L);
   @data_at HCS Tsh t_mident (mident_val (hcr5_IB x25519 R)) (l_ib L);
   hbytes Tsh (r5_rawa R) (l_rawa L); hbytes Tsh (r5_rawb R) (l_rawb L);
   @data_at W_consume_response_any Tsh (tptr t_hnode4) (hcr5_head NS) (l_peers L);
   hbytes Tsh (resp_bytes M) (l_img L); kents_rep W_consume_response_any (hcr5_khead KE) (map (kent_snapped T) KE);
   hcr5_tok t_resp m; resp_rep Ews m M;
   @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st L); hbytes Tsh (resp_bytes M) (l_imga L)] ++
  hcr5_globs gv S FR ++ hcr5_snaps L (hcr5_DAL x25519 R L) head S ++ hcr5_q5_scr L.

Lemma hcr5_q5_A4_QL_eq x25519 gv L FR R S NS PS head T KE m M a P ck h :
  fold_right_sepcon (hcr5_q5_A4_QL x25519 gv L FR R S NS PS head T KE m M a P ck h) =
  itable Tsh (l_ita L) T * (hnodes_rep4 W_consume_response_any (hcr5_head NS) (hnodes_snapped4 T NS PS) *
  (peers_rep (supd PS a (hcr5_q5_put P M ck h)) *
   fold_right_sepcon (hcr5_q5_A4_QR x25519 gv L FR R S NS head KE T m M ck h))).
Proof.
  unfold hcr5_q5_A4_QL, hcr5_q5_A4_QR, hcr5_world. cbn [app fold_right_sepcon].
  apply pred_ext; cancel.
Qed.

(* three abstract openings combined *)
Lemma hcr5_q5_A4_comb (A B D Rst C1 C2 C3 Y: mpred) :
  (A |-- C1 * (C1 -* A)) -> (D |-- C3 * (C3 -* D)) -> (B |-- C2 * (C2 -* B)) ->
  (A * (B * (D * Rst)) |-- Y) ->
  A * (B * (D * Rst)) |-- (C1 * (C3 * C2)) * ((C1 * (C3 * C2)) -* Y).
Proof.
  intros HA HD HB HY.
  sep_apply HA. sep_apply HD. sep_apply HB.
  cancel. rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact HY].
  sep_apply (modus_ponens_wand C1 A). sep_apply (modus_ponens_wand C3 D). sep_apply (modus_ponens_wand C2 B).
  cancel.
Qed.

(* the snapshot's rest (the fields the CHECK does not read) *)
Definition hcr5_q5_A4_srest (y: val) (H: handshake) : mpred :=
  spacer Ews 17 20 y *
  field_at Ews t_hsnap (DOT HR5._state) (Vint (hs_state H)) y *
  data_at Ews (tarray tuchar 32) (bytes (hs_reph H)) (field_address t_hsnap (DOT HR5._remote_ephemeral) y) *
  data_at Ews (tarray tuchar 32) (bytes (hs_hash H)) (field_address t_hsnap (DOT HR5._hash) y) *
  data_at Ews (tarray tuchar 32) (bytes (hs_ck H)) (field_address t_hsnap (DOT HR5._chaining_key) y) *
  field_at Ews t_hsnap (DOT HR5._remote_index) (Vint (hs_rindex H)) y.

Lemma hcr5_q5_A4_snap_eqF y T hh E H : hs_ok H ->
  @data_at W_consume_response_any Ews t_hsnap (hsnap_val (snap_of T hh E H)) y =
  !! (@field_compatible W_consume_response_any t_hsnap [] y) &&
  (fold_right_sepcon (hcr5_q5_A4_Cs y (e_peer E) (succ_in (t_L T) hh) (vin hh (t_L T))
     (e_type E) (e_index E) (hs_sid H) (hs_lic H) (hs_eph H) (hs_rstatic H) (hs_ss H) (hs_psk H) (hs_ts H)) *
   hcr5_q5_A4_srest y H).
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  rewrite hcr5_q5_A4_hsnap_eq, hcr5_q5_A4_snap_split.
  rewrite (hcr5_q5_A4_hb Ews 32 (hs_eph H)), (hcr5_q5_A4_hb Ews 32 (hs_rstatic H)),
    (hcr5_q5_A4_hb Ews 32 (hs_ss H)), (hcr5_q5_A4_hb Ews 32 (hs_psk H)), (hcr5_q5_A4_hb Ews 12 (hs_ts H)) by auto.
  unfold hcr5_q5_A4_Cs, hcr5_q5_A4_srest. cbn [fold_right_sepcon].
  apply pred_ext.
  - assert_PROP (@field_compatible W_consume_response_any t_hsnap (DOT HR5._peer) y) as Hf by entailer!.
    apply andp_right; [apply prop_right; destruct Hf as (A1 & A2 & A3 & A4 & _); repeat split; auto | cancel].
  - Intros. cancel.
Qed.

Lemma hcr5_q5_A4_snap_acc (V: @reptype CKS t_hsnap) y T hh E H :
  V = hsnap_val (snap_of T hh E H) -> hs_ok H ->
  hcr5_q5_A4_acc
    (fold_right_sepcon (hcr5_q5_A4_Cs y (e_peer E) (succ_in (t_L T) hh) (vin hh (t_L T))
       (e_type E) (e_index E) (hs_sid H) (hs_lic H) (hs_eph H) (hs_rstatic H) (hs_ss H) (hs_psk H) (hs_ts H)))
    (@data_at W_consume_response_any Ews t_hsnap V y).
Proof.
  intros HV Hok. subst V. eapply hcr5_q5_A4_acc_wopen. apply hcr5_q5_A4_snap_eqF; exact Hok.
Qed.

(* the node's snapshot fields, out of the node list *)
Lemma hcr5_q5_A4_cnode l NSs N t T hh E H :
  In N NSs -> hn_addr N = t -> hn_snap N = hsnap_val (snap_of T hh E H) -> hs_ok H ->
  hnodes_rep4 W_consume_response_any l NSs |--
  fold_right_sepcon (hcr5_q5_A4_Cs (offset_val 8 t) (e_peer E) (succ_in (t_L T) hh) (vin hh (t_L T))
       (e_type E) (e_index E) (hs_sid H) (hs_lic H) (hs_eph H) (hs_rstatic H) (hs_ss H) (hs_psk H) (hs_ts H)) *
  (fold_right_sepcon (hcr5_q5_A4_Cs (offset_val 8 t) (e_peer E) (succ_in (t_L T) hh) (vin hh (t_L T))
       (e_type E) (e_index E) (hs_sid H) (hs_lic H) (hs_eph H) (hs_rstatic H) (hs_ss H) (hs_psk H) (hs_ts H)) -*
   hnodes_rep4 W_consume_response_any l NSs).
Proof.
  intros Hin Ht HNs Hok. subst t.
  apply (hcr5_q5_A4_nodes_acc _ N NSs l Hin). intros nx. unfold hcr5_q5_A4_nv.
  eapply hcr5_q5_A4_acc_trans; [| apply hcr5_q5_A4_nfld_snap].
  apply hcr5_q5_A4_acc_pure with (c := @field_compatible CKS t_hnode4 [] (hn_addr N)); [apply hcr5_q5_A4_snapfc|].
  intros FC. rewrite (hcr5_q5_A4_snap_at _ _ FC).
  exact (hcr5_q5_A4_snap_acc (hn_snap N) (offset_val 8 (hn_addr N)) T hh E H HNs Hok).
Qed.

Lemma hcr5_q5_A4_peer_putF a P M ck h :
  peer_rep Ews a (hcr5_q5_put P M ck h) =
  !! (@field_compatible Noise.CS t_peer [] a /\ hs_ok (p_hs (hcr5_q5_put P M ck h))) &&
  (fold_right_sepcon (hcr5_q5_A4_Cp (hs_addr a) (hs_sid (p_hs P)) (hs_lic (p_hs P)) (hs_eph (p_hs P))
     (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P)) (hs_ts (p_hs P))) *
   hcr5_q5_A4_prest a (hcr5_q5_put P M ck h)).
Proof.
  rewrite hcr5_q5_A4_peer_put. unfold hcr5_q5_A4_Cp. cbn [fold_right_sepcon].
  apply pred_ext; Intros; (apply andp_right; [apply prop_right; auto | cancel]).
Qed.

Lemma hcr5_q5_A4_itable_eqF sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
  (fold_right_sepcon (hcr5_q5_A4_Ce (hs_addr p) she (e_peer E) (succ_in (t_L T) (hs_addr p))
     (vin (hs_addr p) (t_L T)) (e_type E) (e_index E)) *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros Hfc HwfT HS. rewrite (hcr5_q5_A4_itable_eq sht tab T p she E Hfc HwfT HS).
  unfold hcr5_q5_A4_Ce. cbn [fold_right_sepcon]. rewrite sepcon_emp. reflexivity.
Qed.

Lemma hcr5_q5_A4_cpeerY PS a P M ck h (Y: mpred) : sfind PS a = Some (Ews, P) ->
  (peers_rep (supd PS a (hcr5_q5_put P M ck h)) |-- Y) ->
  peers_rep (supd PS a (hcr5_q5_put P M ck h)) |-- fold_right_sepcon (hcr5_q5_A4_Cp (hs_addr a) (hs_sid (p_hs P)) (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P)) (hs_ts (p_hs P))) * (fold_right_sepcon (hcr5_q5_A4_Cp (hs_addr a) (hs_sid (p_hs P)) (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P)) (hs_ts (p_hs P))) -* Y).
Proof.
  intros Hsf HY. rewrite (hcr5_q5_A4_peers PS a Ews P _ Hsf).
  sep_apply (hcr5_q5_A4_wopen _ _ _ _ (hcr5_q5_A4_peer_putF a P M ck h)). Intros.
  cancel.
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact HY].
  rewrite (hcr5_q5_A4_peers PS a Ews P _ Hsf).
  match goal with |- context [(?C -* peer_rep ?a1 ?a2 ?a3)] => sep_apply (modus_ponens_wand C (peer_rep a1 a2 a3)) end.
  cancel.
Qed.

Lemma hcr5_q5_A4_cpeer PS a P M ck h : sfind PS a = Some (Ews, P) ->
  peers_rep (supd PS a (hcr5_q5_put P M ck h)) |--
  fold_right_sepcon (hcr5_q5_A4_Cp (hs_addr a) (hs_sid (p_hs P)) (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P)) (hs_ts (p_hs P))) * (fold_right_sepcon (hcr5_q5_A4_Cp (hs_addr a) (hs_sid (p_hs P)) (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P)) (hs_ts (p_hs P))) -* peers_rep (supd PS a (hcr5_q5_put P M ck h))).
Proof. intros. apply hcr5_q5_A4_cpeerY; auto. Qed.

Lemma hcr5_q5_A4_citableY sht tab T a she E (Y: mpred) :
  @field_compatible Noise.CS t_peer [] a -> itable_wf T -> sfind (t_D T) (hs_addr a) = Some (she, E) ->
  (itable sht tab T |-- Y) ->
  itable sht tab T |-- fold_right_sepcon (hcr5_q5_A4_Ce (hs_addr a) she (e_peer E) (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E)) * (fold_right_sepcon (hcr5_q5_A4_Ce (hs_addr a) she (e_peer E) (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E)) -* Y).
Proof.
  intros Hfc HwfT HS HY.
  sep_apply (hcr5_q5_A4_wopen2 _ _ _ _ (hcr5_q5_A4_itable_eqF sht tab T a she E Hfc HwfT HS)).
  cancel.
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact HY].
  match goal with |- context [(?C -* itable ?a1 ?a2 ?a3)] => sep_apply (modus_ponens_wand C (itable a1 a2 a3)) end.
  apply derives_refl.
Qed.

Lemma hcr5_q5_A4_citable sht tab T a she E :
  @field_compatible Noise.CS t_peer [] a -> itable_wf T -> sfind (t_D T) (hs_addr a) = Some (she, E) ->
  itable sht tab T |-- fold_right_sepcon (hcr5_q5_A4_Ce (hs_addr a) she (e_peer E) (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E)) * (fold_right_sepcon (hcr5_q5_A4_Ce (hs_addr a) she (e_peer E) (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E)) -* itable sht tab T).
Proof. intros. apply hcr5_q5_A4_citableY; auto. Qed.

(* QA1's SEP gives the twenty fields and a wand back to (anything below) it *)

(* QA1's SEP gives the twenty fields and a wand back to (anything below) it *)
Lemma hcr5_q5_A4_open x25519 gv L FR R S NS PS head T KE m M a P ck h N E she (Y: mpred) :
  itable_wf T -> sfind PS a = Some (Ews, P) -> In N (hnodes_snapped4 T NS PS) ->
  hn_addr N = hcr5_nfind NS a -> hn_snap N = hsnap_val (snap_of T (hs_addr a) E (p_hs P)) ->
  sfind (t_D T) (hs_addr a) = Some (she, E) -> hs_ok (p_hs P) ->
  @field_compatible Noise.CS t_peer [] a ->
  (fold_right_sepcon (hcr5_q5_A4_QL x25519 gv L FR R S NS PS head T KE m M a P ck h) |-- Y) ->
  fold_right_sepcon (hcr5_q5_A4_QL x25519 gv L FR R S NS PS head T KE m M a P ck h) |--
  fold_right_sepcon (hcr5_q5_A4_C (hs_addr a) (offset_val 8 (hcr5_nfind NS a)) she (e_peer E)
      (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E) (hs_sid (p_hs P))
      (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))
      (hs_ts (p_hs P)) ++
    [fold_right_sepcon (hcr5_q5_A4_C (hs_addr a) (offset_val 8 (hcr5_nfind NS a)) she (e_peer E)
      (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E) (hs_sid (p_hs P))
      (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))
      (hs_ts (p_hs P))) -* Y]).
Proof.
  intros HwfT Hsf HIn HNa HNs HS Hok Hfc HY.
  rewrite fold_right_sepcon_app. cbn [fold_right_sepcon]. rewrite sepcon_emp.
  unfold hcr5_q5_A4_C. rewrite !fold_right_sepcon_app.
  rewrite hcr5_q5_A4_QL_eq in *.
  apply hcr5_q5_A4_comb; [ apply hcr5_q5_A4_citable; auto | apply hcr5_q5_A4_cpeer; auto
                        | apply (hcr5_q5_A4_cnode _ _ N); auto | exact HY ].
Qed.

Lemma hcr5_q5_A4_mp (Cl: list mpred) (Y: mpred) :
  fold_right_sepcon (Cl ++ [fold_right_sepcon Cl -* Y]) |-- Y.
Proof. rewrite fold_right_sepcon_app. cbn [fold_right_sepcon]. rewrite sepcon_emp. apply modus_ponens_wand. Qed.

Lemma hcr5_q5_A4_vp_peers PS a P Q R : sfind PS a = Some (Ews, P) ->
  peers_rep (supd PS a Q) * R |-- valid_pointer a.
Proof.
  intros Hf. rewrite (hcr5_q5_A4_peers PS a Ews P Q Hf), hcr5_q5_A4_peer_eq.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. Intros.
  apply sepcon_valid_pointer2. unfold hcr5_q5_A4_prest. apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

(* valid pointers: from one item of a SEP list *)
Lemma hcr5_q5_A4_in_vp (Rl: list mpred) (A: mpred) (x: val) :
  In A Rl -> (A * TT |-- valid_pointer x) -> fold_right_sepcon Rl |-- valid_pointer x.
Proof.
  intros HIn HA. apply in_split in HIn. destruct HIn as (l1 & l2 & ->).
  rewrite fold_right_sepcon_app. simpl. eapply derives_trans; [| exact HA].
  rewrite <- sepcon_assoc, (sepcon_comm (fold_right_sepcon l1) A), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Ltac hcr5_q5_A4_in :=
  cbn [hcr5_q5_A4_QL hcr5_world hcr5_globs hcr5_snaps hcr5_q5_scr app In];
  repeat (first [left; reflexivity | right]).

Lemma hcr5_q5_A4_hv x25519 gv L FR R S NS PS head T KE m M a P ck h E she :
  itable_wf T -> sfind PS a = Some (Ews, P) -> e_peer E = a -> hs_sid (p_hs P) = id_addr (l_wa L) ->
  forall x, In x [e_peer E; succ_in (t_L T) (hs_addr a); hs_sid (p_hs P)] ->
  fold_right_sepcon (hcr5_q5_A4_S (hs_addr a) (offset_val 8 (hcr5_nfind NS a)) she (e_peer E)
      (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E) (hs_sid (p_hs P))
      (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))
      (hs_ts (p_hs P))
      (fold_right_sepcon (hcr5_q5_A4_C (hs_addr a) (offset_val 8 (hcr5_nfind NS a)) she (e_peer E)
         (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T)) (e_type E) (e_index E) (hs_sid (p_hs P))
         (hs_lic (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (hs_ss (p_hs P)) (hs_psk (p_hs P))
         (hs_ts (p_hs P))) -*
       fold_right_sepcon (hcr5_q5_A4_QL x25519 gv L FR R S NS PS head T KE m M a P ck h)))
  |-- valid_pointer x.
Proof.
  intros HwfT Hsf HEp Hsid x Hx.
  rewrite hcr5_q5_A4_S_eq. eapply derives_trans; [apply hcr5_q5_A4_mp |].
  destruct Hx as [<- | [<- | [<- | []]]].
  - apply (hcr5_q5_A4_in_vp _ (peers_rep (supd PS a (hcr5_q5_put P M ck h)))); [hcr5_q5_A4_in |].
    rewrite HEp. apply (hcr5_q5_A4_vp_peers PS a P (hcr5_q5_put P M ck h) TT Hsf).
  - apply (hcr5_q5_A4_in_vp _ (itable Tsh (l_ita L) T)); [hcr5_q5_A4_in |].
    apply (hcr5_q5_A4_vp_tab Tsh (l_ita L) T _ TT (hcr5_q5_A4_succ_in T _ HwfT)).
  - apply (hcr5_q5_A4_in_vp _ (device_rep Tsh (l_wa L) (hcr5_DAL x25519 R L))); [hcr5_q5_A4_in |].
    rewrite Hsid. apply (hcr5_q5_A4_vp_dev Tsh (l_wa L) (hcr5_DAL x25519 R L) TT); auto.
Qed.

(* pure facts of single SEP items *)
Lemma hcr5_q5_A4_sep_prop (Q: list localdef) (Rl: list mpred) (A: mpred) (Pp: Prop) :
  In A Rl -> (A |-- !! Pp) -> PROPx [] (LOCALx Q (SEPx Rl)) |-- !! Pp.
Proof.
  intros HIn HA.
  assert (H1: fold_right_sepcon Rl |-- !! Pp).
  { apply in_split in HIn. destruct HIn as (l1 & l2 & ->). rewrite fold_right_sepcon_app. simpl.
    sep_apply HA. entailer!. }
  intros rho. unfold PROPx, LOCALx, SEPx. simpl. apply andp_left2. apply andp_left2. exact H1.
Qed.

Lemma hcr5_q5_A4_itable_wf sht tab T : itable sht tab T |-- !! itable_wf T.
Proof. unfold itable. Intros. apply prop_right. auto. Qed.

Lemma hcr5_q5_A4_dev_ptr sh wg D : device_rep sh wg D |-- !! isptr wg.
Proof. unfold device_rep. Intros. apply prop_right. destruct H as [Hp _]. exact Hp. Qed.

Lemma hcr5_q5_A4_fc_prop PS a P Q : sfind PS a = Some (Ews, P) ->
  peers_rep (supd PS a Q) |-- !! @field_compatible Noise.CS t_peer [] a.
Proof.
  intros Hf. rewrite (hcr5_q5_A4_peers PS a Ews P Q Hf). unfold peer_rep at 1. Intros.
  apply prop_right. auto.
Qed.

Lemma hcr5_q5_A4_fcs_prop l NSs N : In N NSs ->
  hnodes_rep4 W_consume_response_any l NSs |--
  !! @field_compatible W_consume_response_any t_hsnap [] (offset_val 8 (hn_addr N)).
Proof.
  intros Hin.
  eapply derives_trans; [apply (hcr5_q5_A4_nodes_acc
    (@field_at CKS Ews t_hnode4 [StructField HR5._snap] (hn_snap N) (hn_addr N)) N NSs l Hin);
    intros nx; apply hcr5_q5_A4_nfld_snap |].
  assert_PROP (@field_compatible CKS t_hnode4 [] (hn_addr N)) as FC.
  { eapply derives_trans; [apply sepcon_derives; [apply hcr5_q5_A4_snapfc | apply TT_right] |].
    rewrite prop_sepcon. apply andp_left1. apply derives_refl. }
  rewrite (hcr5_q5_A4_snap_at _ _ FC).
  eapply derives_trans; [apply sepcon_derives; [apply data_at_local_facts | apply TT_right] |].
  rewrite prop_sepcon. apply andp_left1. apply prop_derives. tauto.
Qed.

(* the postcondition: the block lemmas' state gives QA1's SEP back *)
Lemma hcr5_q5_A4_prop_intro (Ps: list Prop) (Q: list localdef) (Rl: list mpred) :
  fold_right and True Ps -> PROPx [] (LOCALx Q (SEPx Rl)) |-- PROPx Ps (LOCALx Q (SEPx Rl)).
Proof.
  intros HP rho. unfold PROPx. simpl. apply andp_derives; [| apply derives_refl].
  apply prop_derives. intros _. exact HP.
Qed.

