(* law handshake: main's phase P2, segment D (statements 51..58): hhs3_p2_SC x25519 aead_enc gv L FR -> hhs3_p2_SC x25519 aead_enc gv L FR.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p2_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

Lemma hhs3_p2_D_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

Lemma hhs3_p2_D_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

#[local] Instance hhs3_p2_D_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

#[local] Instance hhs3_p2_D_CCEH : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

(* the initiation message: its three byte fields as buffers, the rest *)
Section NoiseFields.
#[local] Existing Instance Noise.CS.

Definition hhs3_p2_D_irest (sh: share) (m: val) (M: init_msg) : mpred :=
  field_at sh t_init (DOT I._header) (Vint (im_type M)) m *
  field_at sh t_init (DOT I._sender_index) (Vint (im_sender M)) m *
  field_at sh t_init (DOT I._macs) (bytes (im_mac1 M), bytes (im_mac2 M)) m.

Lemma hhs3_p2_D_init_open sh m M :
  init_rep sh m M =
  !! (im_ok M /\ field_compatible t_init [] m) &&
  (hbytes sh (im_eph M) (offset_val 8 m) * hbytes sh (im_encs M) (offset_val 40 m) *
   hbytes sh (im_enct M) (offset_val 88 m) * hhs3_p2_D_irest sh m M).
Proof.
  unfold init_rep, hhs3_p2_D_irest, init_val. apply pred_ext.
  - Intros. pose proof H as (L1 & L2 & L3 & L4 & L5).
    assert_PROP (field_compatible t_init [] m) as FC by entailer!.
    unfold hbytes. rewrite L1, L2, L3. rewrite !(@hhs3_p2_D_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_init _ m).
    rewrite (field_at_data_at sh t_init (DOT I._unencrypted_ephemeral)),
      (field_at_data_at sh t_init (DOT I._encrypted_static)),
      (field_at_data_at sh t_init (DOT I._encrypted_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros. rename H into Hok, H0 into FC. pose proof Hok as (L1 & L2 & L3 & L4 & L5).
    unfold hbytes. rewrite L1, L2, L3. rewrite !(@hhs3_p2_D_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_init _ m).
    rewrite (field_at_data_at sh t_init (DOT I._unencrypted_ephemeral)),
      (field_at_data_at sh t_init (DOT I._encrypted_static)),
      (field_at_data_at sh t_init (DOT I._encrypted_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.
End NoiseFields.

(* the harness's m_initiation: six byte buffers *)
Lemma hhs3_p2_D_minit_open sh p E encs enct ep ck h :
  @field_compatible HCS t_minit [] p ->
  Zlength E = 32 -> Zlength encs = 48 -> Zlength enct = 28 -> Zlength ep = 32 -> Zlength ck = 32 ->
  Zlength h = 32 ->
  @data_at HCS sh t_minit (minit_val E encs enct ep ck h) p =
  hbytes sh E p * hbytes sh encs (offset_val 32 p) * hbytes sh enct (offset_val 80 p) *
  hbytes sh ep (offset_val 108 p) * hbytes sh ck (offset_val 140 p) * hbytes sh h (offset_val 172 p).
Proof.
  intros FC L1 L2 L3 L4 L5 L6.
  unfold minit_val, hbytes. rewrite L1, L2, L3, L4, L5, L6.
  unfold_data_at (@data_at HCS sh t_minit _ p).
  rewrite (@field_at_data_at HCS sh t_minit (DOT HC._ephemeral)),
    (@field_at_data_at HCS sh t_minit (DOT HC._enc_static)),
    (@field_at_data_at HCS sh t_minit (DOT HC._enc_timestamp)),
    (@field_at_data_at HCS sh t_minit (DOT HC._eph_priv)),
    (@field_at_data_at HCS sh t_minit (DOT HC._st)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (FC2: @field_compatible HCS t_mstate [] (offset_val 140 p)).
  { pose proof (@field_compatible_app HCS [] t_minit (DOT HC._st) p) as X.
    rewrite field_address_offset in X by auto with field_compatible. apply X. simpl app.
    auto with field_compatible. }
  change (Tstruct HH._m_state noattr) with t_mstate.
  unfold_data_at (@data_at HCS sh t_mstate _ (offset_val 140 p)).
  rewrite (@field_at_data_at HCS sh t_mstate (DOT HC._ck)), (@field_at_data_at HCS sh t_mstate (DOT HC._h)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !offset_offset_val. simpl Z.add. rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

(* the peer: its handshake apart; the handshake: eight byte buffers, three scalars, the rest *)
Section NoiseHs.
#[local] Existing Instance Noise.CS.

Definition hhs3_p2_D_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hhs3_p2_D_peer_split sh p P :
  peer_rep sh p P = hhs3_p2_D_prest sh p P * hs_rep sh (hs_addr p) (p_hs P).
Proof.
  unfold peer_rep, hhs3_p2_D_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Definition hhs3_p2_D_hrest (sh: share) (h: val) (H: handshake) : mpred :=
  field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
  (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h.

Definition hhs3_p2_D_hbufs (sh: share) (h: val) (H: handshake) : mpred :=
  hbytes sh (hs_eph H) (offset_val 56 h) * hbytes sh (hs_rstatic H) (offset_val 88 h) *
  hbytes sh (hs_reph H) (offset_val 120 h) * hbytes sh (hs_ss H) (offset_val 152 h) *
  hbytes sh (hs_psk H) (offset_val 184 h) * hbytes sh (hs_hash H) (offset_val 216 h) *
  hbytes sh (hs_ck H) (offset_val 248 h) * hbytes sh (hs_ts H) (offset_val 280 h).

Lemma hhs3_p2_D_hs_open sh h H :
  hs_rep sh h H =
  !! (hs_ok H /\ field_compatible t_hs [] h) &&
  (hhs3_p2_D_hbufs sh h H *
   field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h *
   field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   hhs3_p2_D_hrest sh h H).
Proof.
  unfold hs_rep, hhs3_p2_D_hrest, hhs3_p2_D_hbufs. apply pred_ext.
  - Intros lk. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    assert_PROP (field_compatible t_hs (DOT I._state) h) as FC0 by entailer!.
    assert (FC: field_compatible t_hs [] h) by (destruct FC0 as (?&?&?&?&?); repeat split; auto).
    unfold hbytes. rewrite L1, L2, L3, L4, L5, L6, L7, L8. rewrite !(@hhs3_p2_D_tuchar_cs HCS Noise.CS).
    rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
      (field_at_data_at sh t_hs (DOT I._remote_static)),
      (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
      (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
      (field_at_data_at sh t_hs (DOT I._preshared_key)),
      (field_at_data_at sh t_hs (DOT I._hash)),
      (field_at_data_at sh t_hs (DOT I._chaining_key)),
      (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    Exists lk. entailer!.
  - Intros lk. rename H0 into Hok, H1 into FC. pose proof Hok as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    unfold hbytes. rewrite L1, L2, L3, L4, L5, L6, L7, L8. rewrite !(@hhs3_p2_D_tuchar_cs HCS Noise.CS).
    rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
      (field_at_data_at sh t_hs (DOT I._remote_static)),
      (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
      (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
      (field_at_data_at sh t_hs (DOT I._preshared_key)),
      (field_at_data_at sh t_hs (DOT I._hash)),
      (field_at_data_at sh t_hs (DOT I._chaining_key)),
      (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    Exists lk. entailer!.
Qed.
End NoiseHs.

Lemma hhs3_p2_D_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_handshake (Tstruct HC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_handshake hhs3_p2_D_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hhs3_p2_D_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_handshake (Tstruct HC._wg_peer noattr) [StructField HC._handshake] p = hs_addr p.
Proof. intros H. apply hhs3_p2_D_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hhs3_p2_D_hscs : cs_preserve_type Noise.CS W_handshake (@coeq _ _ hhs3_p2_D_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3_p2_D_state sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state; StructField HC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField HC._state; StructField HC._handshake] with ([StructField HC._state] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state] [StructField HC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hhs3_p2_D_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p2_D_CCE sh t_hs
           [StructField prot_repr3.I._state] (Vint v) (Vint v) (JMeq_refl _) hhs3_p2_D_hscs)).
Qed.

Lemma hhs3_p2_D_rindex sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_index] (Vint v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index; StructField HC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField HC._remote_index; StructField HC._handshake] with ([StructField HC._remote_index] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index] [StructField HC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hhs3_p2_D_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p2_D_CCE sh t_hs
           [StructField prot_repr3.I._remote_index] (Vint v) (Vint v) (JMeq_refl _) hhs3_p2_D_hscs)).
Qed.

Lemma hhs3_p2_D_lic sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr)
    [StructField HC._last_initiation_consumption; StructField HC._handshake] (Vlong v) p.
Proof.
  intros H.
  change [StructField HC._last_initiation_consumption; StructField HC._handshake]
    with ([StructField HC._last_initiation_consumption] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._last_initiation_consumption]
             [StructField HC._handshake] (Vlong v) (Vlong v) p (JMeq_refl _)).
  rewrite hhs3_p2_D_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p2_D_CCE sh t_hs
           [StructField prot_repr3.I._last_initiation_consumption] (Vlong v) (Vlong v) (JMeq_refl _) hhs3_p2_D_hscs)).
Qed.

(* the snapshot: five byte buffers, two scalars at the world, the rest *)
Definition hhs3_p2_D_snrest (sh: share) (p: val) (s: hsnap) : mpred :=
  let E := sn_entry s in let H := sn_hs s in
  @field_at HCS sh t_hsnap (DOT HC._peer) (e_peer E) p *
  @field_at HCS sh t_hsnap (DOT HC._next) (sn_next s) p *
  @field_at HCS sh t_hsnap (DOT HC._hashed) (Val.of_bool (sn_hashed s)) p *
  @field_at HCS sh t_hsnap (DOT HC._type) (Vint (e_type E)) p *
  @field_at HCS sh t_hsnap (DOT HC._index) (Vint (e_index E)) p *
  @field_at HCS sh t_hsnap (DOT HC._state) (Vint (hs_state H)) p *
  @field_at HCS sh t_hsnap (DOT HC._static_identity) (hs_sid H) p *
  @field_at HCS sh t_hsnap (DOT HC._ephemeral_private) (bytes (hs_eph H)) p *
  @field_at HCS sh t_hsnap (DOT HC._hash) (bytes (hs_hash H)) p *
  @field_at HCS sh t_hsnap (DOT HC._chaining_key) (bytes (hs_ck H)) p *
  spacer sh 17 20 p.

Lemma hhs3_p2_D_sncs : cs_preserve_type HCS W_handshake (@coeq _ _ hhs3_p2_D_CCEH) t_hsnap = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3_p2_D_snap_open sh p s :
  @field_compatible HCS t_hsnap [] p ->
  Zlength (hs_rstatic (sn_hs s)) = 32 -> Zlength (hs_reph (sn_hs s)) = 32 -> Zlength (hs_ss (sn_hs s)) = 32 ->
  Zlength (hs_psk (sn_hs s)) = 32 -> Zlength (hs_ts (sn_hs s)) = 12 ->
  @data_at HCS sh t_hsnap (hsnap_val s) p =
  hbytes sh (hs_rstatic (sn_hs s)) (offset_val 80 p) * hbytes sh (hs_reph (sn_hs s)) (offset_val 112 p) *
  hbytes sh (hs_ss (sn_hs s)) (offset_val 144 p) * hbytes sh (hs_psk (sn_hs s)) (offset_val 176 p) *
  hbytes sh (hs_ts (sn_hs s)) (offset_val 272 p) *
  @field_at W_handshake sh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex (sn_hs s))) p *
  @field_at W_handshake sh t_hsnap (DOT HC._last_initiation_consumption) (Vlong (hs_lic (sn_hs s))) p *
  hhs3_p2_D_snrest sh p s.
Proof.
  intros FC L2 L3 L4 L5 L8.
  (* unfold_data_at takes 64 s here; the same steps by hand take 2 s *)
  pose proof (@field_at_Tstruct HCS sh t_hsnap [] HH._hs_snap noattr (hsnap_val s) (hsnap_val s) p eq_refl
                (JMeq_refl _)) as HT.
  simpl co_members in HT. lazy beta iota zeta delta [nested_sfieldlist_at] in HT.
  simpl in HT. unfold withspacer in HT. simpl in HT. unfold hsnap_val in HT. simpl in HT.
  unfold hsnap_val, hhs3_p2_D_snrest, hbytes. rewrite L2, L3, L4, L5, L8.
  unfold data_at at 1. rewrite HT. clear HT.
  rewrite (@field_at_data_at HCS sh t_hsnap (DOT HC._remote_static)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._remote_ephemeral)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._precomputed_static_static)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._preshared_key)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._latest_timestamp)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite <- (@field_at_change_composite HCS W_handshake hhs3_p2_D_CCEH sh t_hsnap (DOT HC._remote_index)
               (Vint (hs_rindex (sn_hs s))) (Vint (hs_rindex (sn_hs s))) (JMeq_refl _) hhs3_p2_D_sncs).
  rewrite <- (@field_at_change_composite HCS W_handshake hhs3_p2_D_CCEH sh t_hsnap (DOT HC._last_initiation_consumption)
               (Vlong (hs_lic (sn_hs s))) (Vlong (hs_lic (sn_hs s))) (JMeq_refl _) hhs3_p2_D_sncs).
  apply pred_ext; cancel.
Qed.

(* the 148-byte image split at 116 (the macs) *)
Lemma hhs3_p2_D_img_split sh bs p :
  Zlength bs = 148 -> @field_compatible HCS (tarray tuchar (Zlength bs)) [] p ->
  hbytes sh bs p = hbytes sh (sublist 0 116 bs) p * hbytes sh (sublist 116 148 bs) (offset_val 116 p).
Proof.
  intros Lb FC. rewrite Lb in FC. unfold hbytes. rewrite !Zlength_sublist by lia. rewrite Lb.
  unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh 148 116) by (try lia; unfold bytes; rewrite Zlength_map; lia).
  rewrite field_address0_offset by auto with field_compatible.
  unfold bytes. rewrite !sublist_map. simpl nested_field_type. simpl nested_field_offset. simpl Z.sub.
  replace (0 + 1 * 116) with 116 by lia. reflexivity.
Qed.

Lemma hhs3_p2_D_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Lemma hhs3_p2_D_init_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (L1 & L2 & L3 & L4 & L5). unfold init_bytes.
  rewrite !Zlength_app, !hhs3_p2_D_le32_len, L1, L2, L3, L4, L5. reflexivity.
Qed.

Lemma hhs3_p2_D_init_macs M : im_ok M -> sublist 116 148 (init_bytes M) = im_mac1 M ++ im_mac2 M.
Proof.
  intros (L1 & L2 & L3 & L4 & L5). unfold init_bytes.
  pose proof (hhs3_p2_D_le32_len (im_type M)). pose proof (hhs3_p2_D_le32_len (im_sender M)).
  list_solve.
Qed.

(* the parameter goal of a bytes_eq call (field addresses of the locals at offset 0) *)
Ltac hhs3_p2_D_par :=
  entailer!;
  try (simpl; unfold hs_addr; rewrite ?offset_offset_val, ?isptr_offset_val_zero by auto with field_compatible;
       reflexivity).

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p2_D_ok {Espec: OracleKind} gv L FR :
  hhs3_p2_agree_stmt x25519 aead_enc ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p2_SC x25519 aead_enc gv L FR) hhs3_p2_D
    (overridePost (hhs3_p2_SC x25519 aead_enc gv L FR) (hhs3_R gv)).
Proof.
  intros HA HH. unfold hhs3_p2_SC, hhs3_Delta, hhs3_R, hhs3_p2_D. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1 MI.
  destruct MI as [[[[[E encs] enct] ep] ck] h].
  destruct HH as (Hx & _).
  pose proof H2 as (Hok & Hci & Hmi & Hfr & Him0 & Hr & Hns).
  pose proof (HA Hx R L I H Hr Hok) as HA'. rewrite Hmi, Hci in HA'. injection HA' as EM EH.
  unfold hhs3_p2_sepB, hhs3_setup_sep, hhs3_globs, hhs3_p2_scr, hhs3_cnt_temps, hhs3_lvars. cbn [app].
  set (P := p_hs (hhs3_PB0 x25519 R L)).
  set (SN := snap_of (hhs3_TA0 L) (hs_addr (l_pb L)) (hhs3_EB L) P).
  assert (ESN: sn_hs SN = P) by reflexivity.
  assert (FE: im_eph M1 = E /\ im_encs M1 = encs /\ im_enct M1 = enct /\ im_mac1 M1 = im_mac1 (i_M0 I) /\
              im_mac2 M1 = im_mac2 (i_M0 I)) by (rewrite EM; repeat split).
  assert (FH: hs_state H1 = HS_CREATED_INITIATION /\ hs_hash H1 = h /\ hs_ck H1 = ck /\ hs_eph H1 = ep /\
              hs_reph H1 = hs_reph P /\ hs_ts H1 = hs_ts P /\ hs_rindex H1 = hs_rindex P /\ hs_lic H1 = hs_lic P /\
              hs_rstatic H1 = hs_rstatic P /\ hs_ss H1 = hs_ss P /\ hs_psk H1 = hs_psk P)
    by (rewrite EH; repeat split).
  destruct FE as (FE1 & FE2 & FE3 & FE4 & FE5).
  destruct FH as (FH1 & FH2 & FH3 & FH4 & FH5 & FH6 & FH7 & FH8 & FH9 & FH10 & FH11).
  (* open m1, pb, mi, snap, img, img_before *)
  rewrite (hhs3_p2_D_init_open Ews m1 M1).
  rewrite (hhs3_p2_D_peer_split Tsh (l_pb L)), (hhs3_p2_D_hs_open Tsh (hs_addr (l_pb L))).
  Intros. rename H4 into ImOk, H5 into FCm1, H6 into HsOk, H7 into FChs.
  change (p_hs (p_set_hs (hhs3_PB0 x25519 R L) H1)) with H1 in *.
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L)) as FCpb.
  { unfold hhs3_p2_D_prest. entailer!. }
  rewrite (hhs3_p2_D_state Tsh (l_pb L) _ FCpb), (hhs3_p2_D_rindex Tsh (l_pb L) _ FCpb),
    (hhs3_p2_D_lic Tsh (l_pb L) _ FCpb).
  pose proof ImOk as (LM1 & LM2 & LM3 & LM4 & LM5).
  pose proof HsOk as (LH1 & LH2 & LH3 & LH4 & LH5 & LH6 & LH7 & LH8).
  assert_PROP (@field_compatible HCS t_minit [] (l_mi L) /\ @field_compatible HCS t_hsnap [] (l_snap L) /\
               @field_compatible HCS (tarray tuchar (Zlength (init_bytes M1))) [] (l_img L) /\
               @field_compatible HCS (tarray tuchar (Zlength (init_bytes (i_M0 I)))) [] (l_imgb L)) as FCs.
  { unfold hbytes. entailer!. }
  destruct FCs as (FCmi & FCsn & FCimg & FCimgb).
  rewrite (hhs3_p2_D_minit_open Tsh (l_mi L) E encs enct ep ck h FCmi) by congruence.
  rewrite (hhs3_p2_D_snap_open Tsh (l_snap L) SN FCsn) by (rewrite ESN; congruence).
  rewrite (hhs3_p2_D_img_split Tsh (init_bytes M1) (l_img L)) by auto using hhs3_p2_D_init_len.
  rewrite (hhs3_p2_D_img_split Tsh (init_bytes (i_M0 I)) (l_imgb L)) by auto using hhs3_p2_D_init_len.
  rewrite (hhs3_p2_D_init_macs M1 ImOk), (hhs3_p2_D_init_macs (i_M0 I) Him0).
  unfold hhs3_p2_D_hbufs. Intros.
  assert (Pm1: isptr m1) by (destruct FCm1; auto).
  (* CHECK(bytes_eq(m1->unencrypted_ephemeral, mi.ephemeral, 32)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 8 m1, im_eph M1, Tsh, l_mi L, E).
    { rewrite LM1. hhs3_p2_D_par. }
    replace (bytes_eqb (im_eph M1) E) with true by (rewrite FE1; symmetry; apply hhs3_p2_D_eqb_refl).
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(m1->encrypted_static, mi.enc_static, 48)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 40 m1, im_encs M1, Tsh, offset_val 32 (l_mi L), encs).
    { rewrite LM2. hhs3_p2_D_par. }
    replace (bytes_eqb (im_encs M1) encs) with true by (rewrite FE2; symmetry; apply hhs3_p2_D_eqb_refl).
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(m1->encrypted_timestamp, mi.enc_timestamp, 28)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 88 m1, im_enct M1, Tsh, offset_val 80 (l_mi L), enct).
    { rewrite LM3. hhs3_p2_D_par. }
    replace (bytes_eqb (im_enct M1) enct) with true by (rewrite FE3; symmetry; apply hhs3_p2_D_eqb_refl).
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(img + 116, img_before + 116, 32)) *)
  assert (LMAC: Zlength (im_mac1 M1 ++ im_mac2 M1) = 32) by (rewrite Zlength_app, LM4, LM5; reflexivity).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 116 (l_img L), im_mac1 M1 ++ im_mac2 M1, Tsh, offset_val 116 (l_imgb L),
                  im_mac1 (i_M0 I) ++ im_mac2 (i_M0 I)).
    { rewrite LMAC. hhs3_p2_D_par. }
    replace (bytes_eqb (im_mac1 M1 ++ im_mac2 M1) (im_mac1 (i_M0 I) ++ im_mac2 (i_M0 I))) with true
      by (rewrite FE4, FE5; symmetry; apply hhs3_p2_D_eqb_refl).
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(pb.handshake.state == HANDSHAKE_CREATED_INITIATION) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward.
    forward_if. { exfalso. rewrite FH1 in *. discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(pb.handshake.hash, mi.st.h, 32) && bytes_eq(pb.handshake.chaining_key, mi.st.ck, 32)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 216 (hs_addr (l_pb L)), hs_hash H1, Tsh, offset_val 172 (l_mi L), h).
    { rewrite LH6. hhs3_p2_D_par. }
    replace (bytes_eqb (hs_hash H1) h) with true by (rewrite FH2; symmetry; apply hhs3_p2_D_eqb_refl).
    forward_if (temp HC._t'42 (Vint Int.one)).
    { forward_call (Tsh, offset_val 248 (hs_addr (l_pb L)), hs_ck H1, Tsh, offset_val 140 (l_mi L), ck).
      { rewrite LH7. hhs3_p2_D_par. }
      replace (bytes_eqb (hs_ck H1) ck) with true by (rewrite FH3; symmetry; apply hhs3_p2_D_eqb_refl).
      forward. entailer!. }
    { exfalso. exact (Int.one_not_zero H4). }
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_eq(pb.handshake.ephemeral_private, mi.eph_priv, 32)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 56 (hs_addr (l_pb L)), hs_eph H1, Tsh, offset_val 108 (l_mi L), ep).
    { rewrite LH1. hhs3_p2_D_par. }
    replace (bytes_eqb (hs_eph H1) ep) with true by (rewrite FH4; symmetry; apply hhs3_p2_D_eqb_refl).
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(remote_ephemeral, latest_timestamp, remote_index, last_initiation_consumption, remote_static,
           precomputed_static_static, preshared_key == snap's) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 120 (hs_addr (l_pb L)), hs_reph H1, Tsh, offset_val 112 (l_snap L), hs_reph (sn_hs SN)).
    { rewrite LH3. hhs3_p2_D_par. }
    all: try (rewrite ESN, <- FH5; rep_lia).
    replace (bytes_eqb (hs_reph H1) (hs_reph (sn_hs SN))) with true
      by (rewrite ESN, FH5; symmetry; apply hhs3_p2_D_eqb_refl).
    forward_if (temp HC._t'46 (Vint Int.one)).
    { forward_call (Tsh, offset_val 280 (hs_addr (l_pb L)), hs_ts H1, Tsh, offset_val 272 (l_snap L), hs_ts (sn_hs SN)).
      { rewrite LH8. hhs3_p2_D_par. }
      all: try (rewrite ESN, <- FH6; rep_lia).
      replace (bytes_eqb (hs_ts H1) (hs_ts (sn_hs SN))) with true
        by (rewrite ESN, FH6; symmetry; apply hhs3_p2_D_eqb_refl).
      forward. entailer!. }
    { exfalso. match goal with Hz: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    forward_if (temp HC._t'48 (Vint Int.one)).
    { forward. forward. forward. entailer!. rewrite ESN, FH7, Int.eq_true. reflexivity. }
    { exfalso. match goal with Hz: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    forward_if (temp HC._t'49 (Vint Int.one)).
    { forward. forward. forward. entailer!. rewrite ESN, FH8, Int64.eq_true. reflexivity. }
    { exfalso. match goal with Hz: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    forward_if (temp HC._t'50 (Vint Int.one)).
    { forward_call (Tsh, offset_val 88 (hs_addr (l_pb L)), hs_rstatic H1, Tsh, offset_val 80 (l_snap L),
                    hs_rstatic (sn_hs SN)).
      { rewrite LH2. hhs3_p2_D_par. }
      all: try (rewrite ESN, <- FH9; rep_lia).
      replace (bytes_eqb (hs_rstatic H1) (hs_rstatic (sn_hs SN))) with true
        by (rewrite ESN, FH9; symmetry; apply hhs3_p2_D_eqb_refl).
      forward. entailer!. }
    { exfalso. match goal with Hz: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    forward_if (temp HC._t'52 (Vint Int.one)).
    { forward_call (Tsh, offset_val 152 (hs_addr (l_pb L)), hs_ss H1, Tsh, offset_val 144 (l_snap L),
                    hs_ss (sn_hs SN)).
      { rewrite LH4. hhs3_p2_D_par. }
      all: try (rewrite ESN, <- FH10; rep_lia).
      replace (bytes_eqb (hs_ss H1) (hs_ss (sn_hs SN))) with true
        by (rewrite ESN, FH10; symmetry; apply hhs3_p2_D_eqb_refl).
      forward. entailer!. }
    { exfalso. match goal with Hz: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    forward_if (temp HC._t'54 (Vint Int.one)).
    { forward_call (Tsh, offset_val 184 (hs_addr (l_pb L)), hs_psk H1, Tsh, offset_val 176 (l_snap L),
                    hs_psk (sn_hs SN)).
      { rewrite LH5. hhs3_p2_D_par. }
      all: try (rewrite ESN, <- FH11; rep_lia).
      replace (bytes_eqb (hs_psk H1) (hs_psk (sn_hs SN))) with true
        by (rewrite ESN, FH11; symmetry; apply hhs3_p2_D_eqb_refl).
      forward. entailer!. }
    { exfalso. match goal with Hz: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* back to SC: open the target the same way *)
  unfold POSTCONDITION, abbreviate. cbv [RA_normal overridePost frame_ret_assert function_body_ret_assert].
  Exists R S m1 m2 a0 f0 l0 I M1 H1 (E, encs, enct, ep, ck, h).
  unfold hhs3_p2_sepB, hhs3_setup_sep, hhs3_globs, hhs3_p2_scr, hhs3_cnt_temps, hhs3_lvars. cbn [app].
  fold P. fold SN.
  rewrite (hhs3_p2_D_init_open Ews m1 M1).
  rewrite (hhs3_p2_D_peer_split Tsh (l_pb L)), (hhs3_p2_D_hs_open Tsh (hs_addr (l_pb L))).
  change (p_hs (p_set_hs (hhs3_PB0 x25519 R L) H1)) with H1.
  rewrite (hhs3_p2_D_state Tsh (l_pb L) _ FCpb), (hhs3_p2_D_rindex Tsh (l_pb L) _ FCpb),
    (hhs3_p2_D_lic Tsh (l_pb L) _ FCpb).
  rewrite (hhs3_p2_D_minit_open Tsh (l_mi L) E encs enct ep ck h FCmi) by congruence.
  rewrite (hhs3_p2_D_snap_open Tsh (l_snap L) SN FCsn) by (rewrite ESN; congruence).
  rewrite (hhs3_p2_D_img_split Tsh (init_bytes M1) (l_img L)) by auto using hhs3_p2_D_init_len.
  rewrite (hhs3_p2_D_img_split Tsh (init_bytes (i_M0 I)) (l_imgb L)) by auto using hhs3_p2_D_init_len.
  rewrite (hhs3_p2_D_init_macs M1 ImOk), (hhs3_p2_D_init_macs (i_M0 I) Him0).
  unfold hhs3_p2_D_hbufs.
  entailer!.
Qed.

End Seg.
