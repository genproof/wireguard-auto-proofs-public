(* law handshake, phase P5, segment D: helpers shared by the parts ca and cb (pb's handshake fields
   as a view: state / remote_index at the world, remote_ephemeral / hash / chaining_key as byte buffers;
   the response message's ephemeral as a buffer). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

#[local] Instance hhs3_p5_D_ca_view_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

#[local] Instance hhs3_p5_D_ca_view_CCEH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

Local Open Scope logic.

Lemma hhs3_p5_D_ca_view_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hhs3_p5_D_ca_view_vp sh d p : sepalg.nonidentity sh ->
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p * TT |-- valid_pointer p.
Proof.
  intros Hsh. apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; vm_compute; reflexivity.
Qed.

Lemma hhs3_p5_D_ca_view_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_handshake (Tstruct HC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_handshake hhs3_p5_D_ca_view_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hhs3_p5_D_ca_view_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_handshake (Tstruct HC._wg_peer noattr) [StructField HC._handshake] p = hs_addr p.
Proof. intros H. apply hhs3_p5_D_ca_view_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hhs3_p5_D_ca_view_fc_hs p f : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible Noise.CS t_peer [StructField f; StructField prot_repr3.I._handshake] p ->
  @field_compatible Noise.CS t_hs [StructField f] (hs_addr p).
Proof.
  intros H H1. apply (field_compatible_app [StructField f] t_peer [StructField prot_repr3.I._handshake]) in H1.
  rewrite field_address_offset in H1 by auto with field_compatible. exact H1.
Qed.

Lemma hhs3_p5_D_ca_view_hscs : cs_preserve_type Noise.CS W_handshake (@coeq _ _ hhs3_p5_D_ca_view_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3_p5_D_ca_view_state sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state; StructField HC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField HC._state; StructField HC._handshake] with ([StructField HC._state] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state] [StructField HC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hhs3_p5_D_ca_view_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p5_D_ca_view_CCE sh t_hs
           [StructField prot_repr3.I._state] (Vint v) (Vint v) (JMeq_refl _) hhs3_p5_D_ca_view_hscs)).
Qed.

Lemma hhs3_p5_D_ca_view_ridx sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_index] (Vint v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index; StructField HC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField HC._remote_index; StructField HC._handshake]
    with ([StructField HC._remote_index] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index] [StructField HC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hhs3_p5_D_ca_view_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p5_D_ca_view_CCE sh t_hs
           [StructField prot_repr3.I._remote_index] (Vint v) (Vint v) (JMeq_refl _) hhs3_p5_D_ca_view_hscs)).
Qed.

Lemma hhs3_p5_D_ca_view_reph sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_ephemeral] (bytes l) (hs_addr p) =
  hbytes sh l (offset_val 168 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p5_D_ca_view_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hhs3_p5_D_ca_view_hash sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._hash] (bytes l) (hs_addr p) = hbytes sh l (offset_val 264 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p5_D_ca_view_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hhs3_p5_D_ca_view_ck sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._chaining_key] (bytes l) (hs_addr p) = hbytes sh l (offset_val 296 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p5_D_ca_view_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

(* the peer without the handshake's state, remote_ephemeral, hash, chaining_key, remote_index *)
Definition hhs3_p5_D_ca_view_other (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._static_identity] (hs_sid H) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._ephemeral_private] (bytes (hs_eph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._preshared_key] (bytes (hs_psk H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._latest_timestamp] (bytes (hs_ts H)) h *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Definition hhs3_p5_D_ca_view (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in
  (@field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state; StructField HC._handshake]
     (Vint (hs_state H)) p *
   @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index; StructField HC._handshake]
     (Vint (hs_rindex H)) p *
   hbytes sh (hs_reph H) (offset_val 168 p) * hbytes sh (hs_hash H) (offset_val 264 p) *
   hbytes sh (hs_ck H) (offset_val 296 p) * hhs3_p5_D_ca_view_other sh p P).

Lemma hhs3_p5_D_ca_view_eq sh p P :
  peer_rep sh p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) && hhs3_p5_D_ca_view sh p P.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (_ & _ & Lr & _ & _ & Lh & Lck & _).
    apply andp_right; [apply prop_right; split; auto |].
    unfold hhs3_p5_D_ca_view, hhs3_p5_D_ca_view_other. cbv zeta.
    rewrite <- (hhs3_p5_D_ca_view_state sh p _ Hfc), <- (hhs3_p5_D_ca_view_ridx sh p _ Hfc),
      <- (hhs3_p5_D_ca_view_reph sh p _ Hfc Lr), <- (hhs3_p5_D_ca_view_hash sh p _ Hfc Lh),
      <- (hhs3_p5_D_ca_view_ck sh p _ Hfc Lck).
    Intros lk. Exists lk. cancel.
  - Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (_ & _ & Lr & _ & _ & Lh & Lck & _).
    unfold hhs3_p5_D_ca_view, hhs3_p5_D_ca_view_other. cbv zeta.
    rewrite <- (hhs3_p5_D_ca_view_state sh p _ Hfc), <- (hhs3_p5_D_ca_view_ridx sh p _ Hfc),
      <- (hhs3_p5_D_ca_view_reph sh p _ Hfc Lr), <- (hhs3_p5_D_ca_view_hash sh p _ Hfc Lh),
      <- (hhs3_p5_D_ca_view_ck sh p _ Hfc Lck).
    unfold peer_rep. Intros lk.
    apply andp_right; [apply prop_right; auto |].
    unfold hs_rep. rewrite (prop_true_andp (hs_ok (p_hs P))) by exact Hok.
    Exists lk. cancel.
Qed.

Lemma hhs3_p5_D_ca_view_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

(* the response message: its ephemeral as a buffer, its sender index at the world, the rest *)
Section NoiseFields.
#[local] Existing Instance Noise.CS.

Definition hhs3_p5_D_ca_view_rrest (sh: share) (m: val) (M: resp_msg) : mpred :=
  field_at sh t_resp (DOT I._header) (Vint (rm_type M)) m *
  field_at sh t_resp (DOT I._receiver_index) (Vint (rm_receiver M)) m *
  field_at sh t_resp (DOT I._encrypted_nothing) (bytes (rm_encn M)) m *
  field_at sh t_resp (DOT I._macs) (bytes (rm_mac1 M), bytes (rm_mac2 M)) m.

Lemma hhs3_p5_D_ca_view_resp sh m M :
  rm_ok M -> field_compatible t_resp [] m ->
  resp_rep sh m M =
  hbytes sh (rm_eph M) (offset_val 12 m) *
  @field_at W_handshake sh (Tstruct HC._message_handshake_response noattr) (DOT HC._sender_index) (Vint (rm_sender M)) m *
  hhs3_p5_D_ca_view_rrest sh m M.
Proof.
  intros Hok FC. unfold resp_rep, hhs3_p5_D_ca_view_rrest, resp_val. rewrite prop_true_andp by exact Hok.
  pose proof Hok as (L1 & L2 & L3 & L4).
  unfold hbytes. rewrite L1. rewrite !(@hhs3_p5_D_ca_view_tuchar_cs HCS Noise.CS).
  unfold_data_at (data_at _ t_resp _ m).
  rewrite (field_at_data_at sh t_resp (DOT I._unencrypted_ephemeral)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite (f_equal (fun f => f m) (@field_at_change_composite Noise.CS W_handshake hhs3_p5_D_ca_view_CCE sh t_resp
           (DOT I._sender_index) (Vint (rm_sender M)) (Vint (rm_sender M)) (JMeq_refl _) ltac:(vm_compute; reflexivity))).
  apply pred_ext; cancel.
Qed.
End NoiseFields.

(* the harness's m_state: two byte buffers *)
Lemma hhs3_p5_D_ca_view_mstate sh p ck h :
  @field_compatible HCS t_mstate [] p -> Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p = hbytes sh ck p * hbytes sh h (offset_val 32 p).
Proof.
  intros FC L1 L2.
  unfold mstate_val, hbytes. rewrite L1, L2.
  unfold_data_at (@data_at HCS sh t_mstate _ p).
  rewrite (@field_at_data_at HCS sh t_mstate (DOT HC._ck)), (@field_at_data_at HCS sh t_mstate (DOT HC._h)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

(* pb's handshake after consume_response *)
Lemma hhs3_p5_D_ca_view_new x25519 R L M1 H1 M2 ck h :
  let H := p_hs (p_set_refs (hhs3_p5_new x25519 R L M1 H1 M2 (ck, h)) Int.one) in
  hs_state H = Int.repr 4 /\ hs_reph H = rm_eph M2 /\ hs_hash H = h /\ hs_ck H = ck /\ hs_rindex H = rm_sender M2.
Proof. repeat split; reflexivity. Qed.
