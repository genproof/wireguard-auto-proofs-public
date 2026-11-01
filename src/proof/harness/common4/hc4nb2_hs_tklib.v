(* hc3_body_snap.v's hs_take helpers hc3b_snap_take_... at CSkhnb (hc4a_nb_cs.v, no
   struct blake2s_ctx), for law handshake_clear's unit. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require WgNoise.harness.x_handshake.code.

Module FH := WgNoise.harness.x_handshake.code.

(* ---- helpers (hs_take): the snapshot struct and the handshake's fields at CSkhnb ---- *)
Local Open Scope logic.
Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.

Lemma hc4nb2_hs_tk_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hc4nb2_hs_tk_sfind_In (D: list (val * share * entry)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Section SnapTakeH.
Context {cs1 cs2: compspecs}.
Lemma hc4nb2_hs_tk_fc_cs n p :
  @field_compatible cs1 (tarray tuchar n) [] p <-> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible. simpl. split; intros (? & ? & ? & ? & ?); repeat split; auto;
  unfold align_compatible in *; destruct p; auto;
  (eapply align_compatible_rec_Tarray; intros; eapply align_compatible_rec_Tarray_inv in H2; eauto;
   inv H2; econstructor; eauto).
Qed.
Lemma hc4nb2_hs_tk_data_at_cs sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply hc4nb2_hs_tk_fc_cs.
Qed.
End SnapTakeH.

Section SnapTake.
#[local] Existing Instance CSkhnb.

#[local] Instance hc4nb2_hs_tk_cce_n : change_composite_env Noise.CS CSkhnb.
Proof. make_cs_preserve Noise.CS CSkhnb. Defined.
#[local] Instance hc4nb2_hs_tk_cce_h : change_composite_env HCS CSkhnb.
Proof. make_cs_preserve HCS CSkhnb. Defined.

Lemma hc4nb2_hs_tk_hbytes sh n A x :
  Zlength A = n -> @data_at CSkhnb sh (tarray tuchar n) (bytes A) x = hbytes sh A x.
Proof. intros <-. unfold hbytes. apply hc4nb2_hs_tk_data_at_cs. Qed.

Lemma hc4nb2_hs_tk_hout sh n x :
  @data_at CSkhnb sh (tarray tuchar n) (Zrepeat Vundef n) x = hout sh n x.
Proof. unfold hout, data_at_, field_at_. apply hc4nb2_hs_tk_data_at_cs. Qed.

Lemma hc4nb2_hs_tk_snap_eq shs (a b c d e f g h: val) (l1 l2 l3 l4 l5 l6 l7 l8: list val) (ri: val) s :
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
  repeat match goal with |- context [Z.eq_dec ?x ?y] => destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
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

Definition hc4nb2_hs_tk_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Definition hc4nb2_hs_tk_hsf (sh: share) (h: val) (H: handshake) : mpred :=
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

Lemma hc4nb2_hs_tk_hsf_eq sh h H :
  hs_ok H ->
  hc4nb2_hs_tk_hsf sh h H =
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
  unfold hc4nb2_hs_tk_hsf.
  Local Ltac hc4nb2_hs_tk_cc f v :=
    rewrite (@field_at_change_composite Noise.CS CSkhnb _ _ t_hs (DOT f) v v (JMeq_refl v)) by reflexivity.
  hc4nb2_hs_tk_cc I._state (Vint (hs_state H)). hc4nb2_hs_tk_cc I._last_initiation_consumption (Vlong (hs_lic H)).
  hc4nb2_hs_tk_cc I._static_identity (hs_sid H). hc4nb2_hs_tk_cc I._remote_index (Vint (hs_rindex H)).
  hc4nb2_hs_tk_cc I._ephemeral_private (bytes (hs_eph H)). hc4nb2_hs_tk_cc I._remote_static (bytes (hs_rstatic H)).
  hc4nb2_hs_tk_cc I._remote_ephemeral (bytes (hs_reph H)). hc4nb2_hs_tk_cc I._precomputed_static_static (bytes (hs_ss H)).
  hc4nb2_hs_tk_cc I._preshared_key (bytes (hs_psk H)). hc4nb2_hs_tk_cc I._hash (bytes (hs_hash H)).
  hc4nb2_hs_tk_cc I._chaining_key (bytes (hs_ck H)). hc4nb2_hs_tk_cc I._latest_timestamp (bytes (hs_ts H)).
  rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
    (field_at_data_at sh t_hs (DOT I._remote_static)),
    (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
    (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
    (field_at_data_at sh t_hs (DOT I._preshared_key)),
    (field_at_data_at sh t_hs (DOT I._hash)),
    (field_at_data_at sh t_hs (DOT I._chaining_key)),
    (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
  simpl nested_field_type.
  rewrite (hc4nb2_hs_tk_hbytes sh 32 (hs_eph H)), (hc4nb2_hs_tk_hbytes sh 32 (hs_rstatic H)),
    (hc4nb2_hs_tk_hbytes sh 32 (hs_reph H)), (hc4nb2_hs_tk_hbytes sh 32 (hs_ss H)),
    (hc4nb2_hs_tk_hbytes sh 32 (hs_psk H)), (hc4nb2_hs_tk_hbytes sh 32 (hs_hash H)),
    (hc4nb2_hs_tk_hbytes sh 32 (hs_ck H)), (hc4nb2_hs_tk_hbytes sh 12 (hs_ts H)) by auto.
  reflexivity.
Qed.

Lemma hc4nb2_hs_tk_peer_eq sh p P :
  peer_rep sh p P = hc4nb2_hs_tk_hsf sh (hs_addr p) (p_hs P) * hc4nb2_hs_tk_prest sh p P.
Proof.
  unfold peer_rep, hs_rep, hc4nb2_hs_tk_prest.
  apply pred_ext.
  - Intros. rewrite hc4nb2_hs_tk_hsf_eq by auto. Intros lk. Exists lk. entailer!.
  - Intros lk. rewrite hc4nb2_hs_tk_hsf_eq by auto. entailer!. Exists lk. cancel.
Qed.

Lemma hc4nb2_hs_tk_fc p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_peer [] p.
Proof. intros. apply (@field_compatible_change_composite Noise.CS CSkhnb _ t_peer); auto. Qed.

Lemma hc4nb2_hs_tk_entry_fa sh v p :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at CSkhnb sh t_hs (DOT FH._entry) v (hs_addr p).
Proof.
  intros FC0. pose proof (hc4nb2_hs_tk_fc p FC0) as FC.
  rewrite (@data_at_change_composite Noise.CS CSkhnb _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: field_compatible t_hs (DOT FH._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hc4nb2_hs_tk_open sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
  (@field_at CSkhnb she t_hs (DOT FH._entry) (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p) *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (hc4nb2_hs_tk_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hc4nb2_hs_tk_entry_fa by auto.
  apply pred_ext; entailer!.
Qed.

Lemma hc4nb2_hs_tk_pool_ptrs L (D: list (val * share * entry)) :
  iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [|[[x sh] e] D IH]; simpl.
  - entailer!.
  - assert_PROP (Forall isptr (saddrs D)) as HF by (sep_apply IH; entailer!).
    unfold pool_item_rep at 1, entry_at.
    assert_PROP (isptr x) as Hx by (entailer!; match goal with Hc: field_compatible _ _ x |- _ => destruct Hc; auto end).
    entailer!.
Qed.

Lemma hc4nb2_hs_tk_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

Lemma hc4nb2_hs_tk_succ_ptr T a :
  itable_wf T -> Forall isptr (saddrs (t_D T)) -> is_pointer_or_null (succ_in (t_L T) a).
Proof.
  intros (_ & HI & _) HF. destruct (hc4nb2_hs_tk_succ (t_L T) a) as [-> | Hin]; [simpl; auto|].
  apply HI in Hin. rewrite Forall_forall in HF. apply HF in Hin. destruct (succ_in _ _); try contradiction; exact I.
Qed.

Lemma hc4nb2_hs_tk_fcs shs s :
  @data_at_ HCS shs t_hsnap s |-- !! field_compatible t_hsnap [] s.
Proof.
  rewrite (@data_at__change_composite HCS CSkhnb _ shs t_hsnap) by reflexivity. entailer!.
Qed.

Lemma hc4nb2_hs_tk_fch p :
  @field_compatible Noise.CS t_peer [] p -> field_compatible t_hs [] (hs_addr p).
Proof.
  intros FC0. pose proof (hc4nb2_hs_tk_fc p FC0) as FC.
  assert (FC1: field_compatible t_peer (DOT FH._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in FC1. exact FC1.
Qed.

End SnapTake.
