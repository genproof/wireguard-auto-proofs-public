(* law handshake, phase P3, segment D, part ca: helpers (pa's handshake fields as a view: state at the
   world, remote_ephemeral / latest_timestamp as byte buffers; the initiation message's ephemeral as a buffer;
   the harness's ci with its ts as a buffer).  Adapted from hhs3_p5_D_ca_view.v. *)
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

#[local] Instance hhs3_p3_D_ca_view_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

#[local] Instance hhs3_p3_D_ca_view_CCEH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

Local Open Scope logic.

Lemma hhs3_p3_D_ca_view_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hhs3_p3_D_ca_view_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_handshake (Tstruct HC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_handshake hhs3_p3_D_ca_view_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hhs3_p3_D_ca_view_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_handshake (Tstruct HC._wg_peer noattr) [StructField HC._handshake] p = hs_addr p.
Proof. intros H. apply hhs3_p3_D_ca_view_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hhs3_p3_D_ca_view_fc_hs p f : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible Noise.CS t_peer [StructField f; StructField prot_repr3.I._handshake] p ->
  @field_compatible Noise.CS t_hs [StructField f] (hs_addr p).
Proof.
  intros H H1. apply (field_compatible_app [StructField f] t_peer [StructField prot_repr3.I._handshake]) in H1.
  rewrite field_address_offset in H1 by auto with field_compatible. exact H1.
Qed.

Lemma hhs3_p3_D_ca_view_hscs : cs_preserve_type Noise.CS W_handshake (@coeq _ _ hhs3_p3_D_ca_view_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3_p3_D_ca_view_state sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state; StructField HC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField HC._state; StructField HC._handshake] with ([StructField HC._state] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state] [StructField HC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hhs3_p3_D_ca_view_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p3_D_ca_view_CCE sh t_hs
           [StructField prot_repr3.I._state] (Vint v) (Vint v) (JMeq_refl _) hhs3_p3_D_ca_view_hscs)).
Qed.

Lemma hhs3_p3_D_ca_view_reph sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_ephemeral] (bytes l) (hs_addr p) =
  hbytes sh l (offset_val 168 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p3_D_ca_view_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hhs3_p3_D_ca_view_ts sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 12 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._latest_timestamp] (bytes l) (hs_addr p) =
  hbytes sh l (offset_val 328 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p3_D_ca_view_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

(* the peer without the handshake's state, remote_ephemeral, latest_timestamp *)
Definition hhs3_p3_D_ca_view_other (sh: share) (p: val) (P: peer) : mpred :=
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
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._hash] (bytes (hs_hash H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._chaining_key] (bytes (hs_ck H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Definition hhs3_p3_D_ca_view (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in
  (@field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state; StructField HC._handshake]
     (Vint (hs_state H)) p *
   hbytes sh (hs_reph H) (offset_val 168 p) * hbytes sh (hs_ts H) (offset_val 328 p) *
   hhs3_p3_D_ca_view_other sh p P).

Lemma hhs3_p3_D_ca_view_eq sh p P :
  peer_rep sh p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) && hhs3_p3_D_ca_view sh p P.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (_ & _ & Lr & _ & _ & _ & _ & Lt).
    apply andp_right; [apply prop_right; split; auto |].
    unfold hhs3_p3_D_ca_view, hhs3_p3_D_ca_view_other. cbv zeta.
    rewrite <- (hhs3_p3_D_ca_view_state sh p _ Hfc),
      <- (hhs3_p3_D_ca_view_reph sh p _ Hfc Lr), <- (hhs3_p3_D_ca_view_ts sh p _ Hfc Lt).
    Intros lk. Exists lk. cancel.
  - Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (_ & _ & Lr & _ & _ & _ & _ & Lt).
    unfold hhs3_p3_D_ca_view, hhs3_p3_D_ca_view_other. cbv zeta.
    rewrite <- (hhs3_p3_D_ca_view_state sh p _ Hfc),
      <- (hhs3_p3_D_ca_view_reph sh p _ Hfc Lr), <- (hhs3_p3_D_ca_view_ts sh p _ Hfc Lt).
    unfold peer_rep. Intros lk.
    apply andp_right; [apply prop_right; auto |].
    unfold hs_rep. rewrite (prop_true_andp (hs_ok (p_hs P))) by exact Hok.
    Exists lk. cancel.
Qed.

Lemma hhs3_p3_D_ca_view_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

(* the initiation message: its ephemeral as a buffer, the rest *)
Section NoiseFields.
#[local] Existing Instance Noise.CS.

Definition hhs3_p3_D_ca_view_irest (sh: share) (m: val) (M: init_msg) : mpred :=
  field_at sh t_init (DOT I._header) (Vint (im_type M)) m *
  field_at sh t_init (DOT I._sender_index) (Vint (im_sender M)) m *
  field_at sh t_init (DOT I._encrypted_static) (bytes (im_encs M)) m *
  field_at sh t_init (DOT I._encrypted_timestamp) (bytes (im_enct M)) m *
  field_at sh t_init (DOT I._macs) (bytes (im_mac1 M), bytes (im_mac2 M)) m.

Lemma hhs3_p3_D_ca_view_init sh m M :
  init_rep sh m M =
  !! (im_ok M /\ field_compatible t_init [] m) &&
  (hbytes sh (im_eph M) (offset_val 8 m) * hhs3_p3_D_ca_view_irest sh m M).
Proof.
  unfold init_rep, hhs3_p3_D_ca_view_irest, init_val. apply pred_ext.
  - Intros. pose proof H as (L1 & L2 & L3 & L4 & L5).
    assert_PROP (field_compatible t_init [] m) as FC by entailer!.
    unfold hbytes. rewrite L1. rewrite !(@hhs3_p3_D_ca_view_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_init _ m).
    rewrite (field_at_data_at sh t_init (DOT I._unencrypted_ephemeral)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros. rename H into Hok, H0 into FC. pose proof Hok as (L1 & L2 & L3 & L4 & L5).
    unfold hbytes. rewrite L1. rewrite !(@hhs3_p3_D_ca_view_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_init _ m).
    rewrite (field_at_data_at sh t_init (DOT I._unencrypted_ephemeral)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.
End NoiseFields.

(* the harness's ci: its ts as a buffer, the rest *)
Section HCSFields.
#[local] Existing Instance HCS.

Definition hhs3_p3_D_ca_view_cirest (sh: share) (ci: val) (ck h: list byte) (kv sv: list val) : mpred :=
  field_at sh t_mcinit (DOT HC._st) (bytes ck, bytes h) ci *
  field_at sh t_mcinit (DOT HC._key) kv ci *
  field_at sh t_mcinit (DOT HC._spub) sv ci.

Lemma hhs3_p3_D_ca_view_ci sh ci ck h kv sv t :
  field_compatible t_mcinit [] ci -> Zlength t = 12 ->
  data_at sh t_mcinit (mcinit_val ck h kv sv (bytes t)) ci =
  hbytes sh t (offset_val 128 ci) * hhs3_p3_D_ca_view_cirest sh ci ck h kv sv.
Proof.
  intros Hfc Lt. unfold mcinit_val, hbytes, hhs3_p3_D_ca_view_cirest. rewrite Lt.
  unfold_data_at (data_at _ t_mcinit _ ci).
  rewrite (field_at_data_at sh t_mcinit (DOT HC._ts)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  apply pred_ext; cancel.
Qed.
End HCSFields.

(* pa's handshake after consume_initiation (and the put) *)
Lemma hhs3_p3_D_ca_view_new x25519 R L M1 nowb t ck h :
  let H := p_hs (hhs3_PA2 (hhs3_p3_new x25519 R L M1 nowb (t, ck, h))) in
  hs_state H = Int.repr 2 /\ hs_reph H = im_eph M1 /\ hs_ts H = t.
Proof. repeat split; reflexivity. Qed.

Lemma hhs3_p3_D_ca_view_M1eph x25519 R M1 : im_eph (hhs3_M1m x25519 R M1) = im_eph M1.
Proof. reflexivity. Qed.
