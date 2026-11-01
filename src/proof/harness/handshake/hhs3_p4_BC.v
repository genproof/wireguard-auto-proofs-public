(* law handshake, phase P4, segment BC.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p4_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

Lemma hhs3_p4_BC_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

Lemma hhs3_p4_BC_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hhs3_p4_BC_wand_eq (P Q C: mpred) (X: Prop) : P = !!X && (Q * C) -> P |-- Q * (Q -* P).
Proof.
  intros E. rewrite E at 1. Intros. cancel. apply wand_sepcon_adjoint. rewrite E. entailer!.
Qed.

Lemma hhs3_p4_BC_tsplit bs p : hbytes Tsh bs p = hbytes Ews bs p * hbytes (Share.comp Ews) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

Lemma hhs3_p4_BC_clamp_len r : Zlength r = 32 -> Zlength (clamp r) = 32.
Proof. intros. unfold clamp. list_solve. Qed.

Lemma hhs3_p4_BC_b2s_len key m : Zlength (model.blake2s key 32 m) = 32.
Proof. unfold model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hhs3_p4_BC_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac, HASH. apply hhs3_p4_BC_b2s_len. Qed.

Lemma hhs3_p4_BC_hout32 sh bs p : Zlength bs = 32 -> hbytes sh bs p |-- hout sh 32 p.
Proof. intros <-. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hhs3_p4_BC_hif sh (b: bool) bs p : Zlength bs = 32 ->
  (if b then hbytes sh bs p else hout sh 32 p) |-- hout sh 32 p.
Proof. intros Hl. destruct b; [apply hhs3_p4_BC_hout32; exact Hl | apply derives_refl]. Qed.

(* m1's ephemeral, with a wand back *)
Section NoiseFields.
#[local] Existing Instance Noise.CS.

Definition hhs3_p4_BC_irest (sh: share) (m: val) (M: init_msg) : mpred :=
  field_at sh t_init (DOT I._header) (Vint (im_type M)) m *
  field_at sh t_init (DOT I._sender_index) (Vint (im_sender M)) m *
  field_at sh t_init (DOT I._macs) (bytes (im_mac1 M), bytes (im_mac2 M)) m.

Lemma hhs3_p4_BC_init_open sh m M :
  init_rep sh m M =
  !! (im_ok M /\ field_compatible t_init [] m) &&
  (hbytes sh (im_eph M) (offset_val 8 m) * hbytes sh (im_encs M) (offset_val 40 m) *
   hbytes sh (im_enct M) (offset_val 88 m) * hhs3_p4_BC_irest sh m M).
Proof.
  unfold init_rep, hhs3_p4_BC_irest, init_val. apply pred_ext.
  - Intros. pose proof H as (L1 & L2 & L3 & L4 & L5).
    assert_PROP (field_compatible t_init [] m) as FC by entailer!.
    unfold hbytes. rewrite L1, L2, L3. rewrite !(@hhs3_p4_BC_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_init _ m).
    rewrite (field_at_data_at sh t_init (DOT I._unencrypted_ephemeral)),
      (field_at_data_at sh t_init (DOT I._encrypted_static)),
      (field_at_data_at sh t_init (DOT I._encrypted_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros. rename H into Hok, H0 into FC. pose proof Hok as (L1 & L2 & L3 & L4 & L5).
    unfold hbytes. rewrite L1, L2, L3. rewrite !(@hhs3_p4_BC_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_init _ m).
    rewrite (field_at_data_at sh t_init (DOT I._unencrypted_ephemeral)),
      (field_at_data_at sh t_init (DOT I._encrypted_static)),
      (field_at_data_at sh t_init (DOT I._encrypted_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.

Lemma hhs3_p4_BC_eph_open sh m M :
  init_rep sh m M |-- hbytes sh (im_eph M) (offset_val 8 m) * (hbytes sh (im_eph M) (offset_val 8 m) -* init_rep sh m M).
Proof.
  apply (hhs3_p4_BC_wand_eq _ _
    (hbytes sh (im_encs M) (offset_val 40 m) * hbytes sh (im_enct M) (offset_val 88 m) * hhs3_p4_BC_irest sh m M)
    (im_ok M /\ field_compatible t_init [] m)).
  rewrite hhs3_p4_BC_init_open. f_equal. apply pred_ext; cancel.
Qed.
End NoiseFields.

(* pa's remote static (its handshake apart), with a wand back *)
Section NoiseHs.
#[local] Existing Instance Noise.CS.

Definition hhs3_p4_BC_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Lemma hhs3_p4_BC_peer_split sh p P :
  peer_rep sh p P = hhs3_p4_BC_prest sh p P * hs_rep sh (hs_addr p) (p_hs P).
Proof.
  unfold peer_rep, hhs3_p4_BC_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Definition hhs3_p4_BC_hrest (sh: share) (h: val) (H: handshake) : mpred :=
  field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
  (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h.

Definition hhs3_p4_BC_hbufs (sh: share) (h: val) (H: handshake) : mpred :=
  hbytes sh (hs_eph H) (offset_val 56 h) * hbytes sh (hs_rstatic H) (offset_val 88 h) *
  hbytes sh (hs_reph H) (offset_val 120 h) * hbytes sh (hs_ss H) (offset_val 152 h) *
  hbytes sh (hs_psk H) (offset_val 184 h) * hbytes sh (hs_hash H) (offset_val 216 h) *
  hbytes sh (hs_ck H) (offset_val 248 h) * hbytes sh (hs_ts H) (offset_val 280 h).

Lemma hhs3_p4_BC_hs_open sh h H :
  hs_rep sh h H =
  !! (hs_ok H /\ field_compatible t_hs [] h) &&
  (hhs3_p4_BC_hbufs sh h H *
   field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h *
   field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   hhs3_p4_BC_hrest sh h H).
Proof.
  unfold hs_rep, hhs3_p4_BC_hrest, hhs3_p4_BC_hbufs. apply pred_ext.
  - Intros lk. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    assert_PROP (field_compatible t_hs (DOT I._state) h) as FC0 by entailer!.
    assert (FC: field_compatible t_hs [] h) by (destruct FC0 as (?&?&?&?&?); repeat split; auto).
    unfold hbytes. rewrite L1, L2, L3, L4, L5, L6, L7, L8. rewrite !(@hhs3_p4_BC_tuchar_cs HCS Noise.CS).
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
    unfold hbytes. rewrite L1, L2, L3, L4, L5, L6, L7, L8. rewrite !(@hhs3_p4_BC_tuchar_cs HCS Noise.CS).
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

(* the remote static at the share Ews (the rest of Tsh stays in the wand's frame) *)
Lemma hhs3_p4_BC_rs_open h H :
  hs_rep Tsh h H |-- hbytes Ews (hs_rstatic H) (offset_val 88 h) *
                    (hbytes Ews (hs_rstatic H) (offset_val 88 h) -* hs_rep Tsh h H).
Proof.
  apply (hhs3_p4_BC_wand_eq _ _
    (hbytes (Share.comp Ews) (hs_rstatic H) (offset_val 88 h) *
     hbytes Tsh (hs_eph H) (offset_val 56 h) *
     hbytes Tsh (hs_reph H) (offset_val 120 h) * hbytes Tsh (hs_ss H) (offset_val 152 h) *
     hbytes Tsh (hs_psk H) (offset_val 184 h) * hbytes Tsh (hs_hash H) (offset_val 216 h) *
     hbytes Tsh (hs_ck H) (offset_val 248 h) * hbytes Tsh (hs_ts H) (offset_val 280 h) *
     @field_at Noise.CS Tsh t_hs [StructField I._state] (Vint (hs_state H)) h *
     @field_at Noise.CS Tsh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
     @field_at Noise.CS Tsh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
     hhs3_p4_BC_hrest Tsh h H)
    (hs_ok H /\ @field_compatible Noise.CS t_hs [] h)).
  rewrite hhs3_p4_BC_hs_open. unfold hhs3_p4_BC_hbufs.
  rewrite (hhs3_p4_BC_tsplit (hs_rstatic H) (offset_val 88 h)).
  f_equal. apply pred_ext; cancel.
Qed.

(* the shim's random log, with a wand back *)
Lemma hhs3_p4_BC_shim_open gv S :
  shim_state gv S |--
  hbytes Ews (s_log S) (gv _wg_shim_random_log) * (hbytes Ews (s_log S) (gv _wg_shim_random_log) -* shim_state gv S).
Proof.
  assert_PROP (shim_ok S) as Hok by (unfold shim_state; entailer!).
  pose proof Hok as [Ll Lp].
  assert (Eq: hbytes Ews (s_log S) (gv _wg_shim_random_log) =
              @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log)).
  { unfold hbytes. rewrite Ll. apply hhs3_p4_BC_tuchar_cs. }
  apply (hhs3_p4_BC_wand_eq _ _
    (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
     @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
     @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
     @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
     @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
     @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
     @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
     @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
     @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
     @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
     @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv)
    (shim_ok S)).
  rewrite Eq. unfold shim_state. f_equal. apply pred_ext; cancel.
Qed.
End NoiseHs.

(* ci's state (at offset 0), with a wand back *)
Lemma hhs3_p4_BC_ci_st sh p ck h keyv spv tsv :
  @data_at HCS sh t_mcinit (mcinit_val ck h keyv spv tsv) p |--
  @data_at HCS sh t_mstate (mstate_val ck h) p *
  (@data_at HCS sh t_mstate (mstate_val ck h) p -* @data_at HCS sh t_mcinit (mcinit_val ck h keyv spv tsv) p).
Proof.
  apply (hhs3_p4_BC_wand_eq _ _
    (@field_at HCS sh t_mcinit (DOT HC._key) keyv p * @field_at HCS sh t_mcinit (DOT HC._spub) spv p *
     @field_at HCS sh t_mcinit (DOT HC._ts) tsv p)
    (@field_compatible HCS t_mcinit [] p)).
  apply pred_ext.
  - assert_PROP (@field_compatible HCS t_mcinit [] p) as FC by entailer!.
    unfold mcinit_val. unfold_data_at (@data_at HCS sh t_mcinit _ p).
    rewrite (@field_at_data_at HCS sh t_mcinit (DOT HC._st)).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    assert (isptr p) by (destruct FC; auto).
    rewrite (isptr_offset_val_zero p) by auto.
    unfold mstate_val. change (Tstruct HH._m_state noattr) with t_mstate. entailer!.
  - Intros. rename H into FC.
    unfold mcinit_val. unfold_data_at (@data_at HCS sh t_mcinit _ p).
    rewrite (@field_at_data_at HCS sh t_mcinit (DOT HC._st)).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    assert (isptr p) by (destruct FC; auto).
    rewrite (isptr_offset_val_zero p) by auto.
    unfold mstate_val. change (Tstruct HH._m_state noattr) with t_mstate. entailer!.
Qed.

(* mr after m_create_response, its ephemeral and eph_priv as byte buffers *)
Lemma hhs3_p4_BC_mr_open sh p E ep (encv: list val) (stv: list val * list val) :
  @field_compatible HCS t_mresp [] p -> Zlength E = 32 -> Zlength ep = 32 ->
  @data_at HCS sh t_mresp (bytes E, (encv, (bytes ep, stv))) p =
  hbytes sh E p * hbytes sh ep (offset_val 48 p) *
  (@field_at HCS sh t_mresp (DOT HC._enc_nothing) encv p * @field_at HCS sh t_mresp (DOT HC._st) stv p).
Proof.
  intros FC L1 L3.
  unfold hbytes. rewrite L1, L3.
  unfold_data_at (@data_at HCS sh t_mresp _ p).
  rewrite (@field_at_data_at HCS sh t_mresp (DOT HC._ephemeral)),
    (@field_at_data_at HCS sh t_mresp (DOT HC._eph_priv)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

(* the harness's m_initiation: six byte buffers *)
Lemma hhs3_p4_BC_minit_open sh p E encs enct ep ck h :
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

(* the harness's m_identity: priv, pub as byte buffers, the flag *)
Lemma hhs3_p4_BC_mident_open sh p I :
  @field_compatible HCS t_mident [] p -> Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  hbytes sh (mi_priv I) p * hbytes sh (mi_pub I) (offset_val 32 p) *
  @field_at HCS sh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p.
Proof.
  intros FC L1 L2.
  unfold mident_val, hbytes. rewrite L1, L2.
  unfold_data_at (@data_at HCS sh t_mident _ p).
  rewrite (@field_at_data_at HCS sh t_mident (DOT HH._priv)), (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

(* mi: its ephemeral and eph_priv as byte buffers *)
Lemma hhs3_p4_BC_mi_open sh p E ep (encsv enctv: list val) (stv: list val * list val) :
  @field_compatible HCS t_minit [] p -> Zlength E = 32 -> Zlength ep = 32 ->
  @data_at HCS sh t_minit (bytes E, (encsv, (enctv, (bytes ep, stv)))) p =
  hbytes sh E p * hbytes sh ep (offset_val 108 p) *
  (@field_at HCS sh t_minit (DOT HC._enc_static) encsv p * @field_at HCS sh t_minit (DOT HC._enc_timestamp) enctv p *
   @field_at HCS sh t_minit (DOT HC._st) stv p).
Proof.
  intros FC L1 L3.
  unfold hbytes. rewrite L1, L3.
  unfold_data_at (@data_at HCS sh t_minit _ p).
  rewrite (@field_at_data_at HCS sh t_minit (DOT HC._ephemeral)),
    (@field_at_data_at HCS sh t_minit (DOT HC._eph_priv)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

Local Open Scope Z_scope.

(* an equation kept out of reach of subst / entailer! *)
Definition hhs3_p4_BC_hide (P: Prop) : Prop := P.

Tactic Notation "hhs3_p4_BC_rem" constr(t) "as" ident(x) ident(E) :=
  remember t as x eqn:E; change (x = t) with (hhs3_p4_BC_hide (x = t)) in E.

Lemma hhs3_p4_BC_if_false (b: bool) : (if b then Int.one else Int.repr 0) = Int.zero -> b = false.
Proof. destruct b; [intros X; exfalso; apply Int.one_not_zero; exact X | reflexivity]. Qed.

Lemma hhs3_p4_BC_if_true (b: bool) : (if b then Int.one else Int.repr 0) <> Int.zero -> b = true.
Proof. destruct b; [reflexivity | intros X; exfalso; apply X; reflexivity]. Qed.

(* forward_if whose join adds the temp t := v and replaces the SEP item old by new *)
Ltac hhs3_p4_BC_fif t v old new :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    let F := eval pattern old in Rs in
    match F with ?G _ =>
    let Rs' := eval cbv beta in (G new) in
    forward_if (PROPx P (LOCALx (temp t v :: Q) (SEPx Rs')))
    end end.

Section P4BC.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* create_response never changes the remote static *)
Lemma hhs3_p4_BC_cr_rs H M r idx :
  hs_rstatic (snd (create_response_model x25519 aead_enc H M r idx)) = hs_rstatic H.
Proof.
  unfold create_response_model. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma hhs3_p4_BC_cs2_len ss ck h enct t ck2 h2 :
  m_consume_init2_model aead_dec ss ck h enct = Some (t, ck2, h2) -> Zlength ck2 = 32 /\ Zlength h2 = 32.
Proof.
  intros E. unfold m_consume_init2_model, consume_init_stage2 in E. cbn [im_enct] in E.
  destruct (negb _); [discriminate |].
  destruct (aead_dec _ _ _ _) as [t'|] eqn:Ed; [| discriminate].
  injection E as <- <- <-.
  unfold kdf1, mix_hash, HASH. rewrite !hhs3_p4_BC_hmac_len, hhs3_p4_BC_b2s_len. lia.
Qed.

Lemma hhs3_p4_BC_mi_len spub rpub ss eraw ts E encs enct ep ck h :
  x25519_props x25519 -> Zlength eraw = 32 ->
  m_create_initiation_model x25519 aead_enc spub rpub ss eraw ts = Some (E, encs, enct, ep, ck, h) ->
  Zlength E = 32 /\ Zlength ep = 32.
Proof.
  intros Hx Hr E1. unfold m_create_initiation_model in E1. cbv zeta in E1.
  repeat match type of E1 with context [if ?b then _ else _] => destruct b end; try discriminate.
  injection E1 as <- <- <- <- <- <-. split; [apply Hx | apply hhs3_p4_BC_clamp_len; exact Hr].
Qed.

(* mr after the call, in both outcomes: ephemeral = X25519(clamp r, 9), eph_priv = clamp r *)
Lemma hhs3_p4_BC_mr_gen (OMR: option (list byte * list byte * list byte * list byte * list byte)) r p :
  (forall E encn ep ck h, OMR = Some (E, encn, ep, ck, h) -> ep = clamp r /\ E = x25519 ep basepoint9) ->
  match OMR with
  | Some (E, encn, ep, ck, h) => @data_at HCS Tsh t_mresp (mresp_val E encn ep ck h) p
  | None => EX ab: list byte * list byte,
            @data_at HCS Tsh t_mresp (bytes (x25519 (clamp r) basepoint9),
                                      (Zrepeat Vundef 16, (bytes (clamp r), (bytes (fst ab), bytes (snd ab))))) p
  end
  |-- EX encv: list val, EX stv: list val * list val,
      !! (match OMR with Some (E, encn, ep, ck, h) => encv = bytes encn /\ stv = (bytes ck, bytes h)
          | None => True end) &&
      @data_at HCS Tsh t_mresp (bytes (x25519 (clamp r) basepoint9), (encv, (bytes (clamp r), stv))) p.
Proof.
  intros HS. destruct OMR as [[[[[E encn] ep] ck] h]|].
  - destruct (HS E encn ep ck h eq_refl) as [-> ->].
    Exists (bytes encn) (bytes ck, bytes h). unfold mresp_val. entailer!.
  - Intros ab. Exists (Zrepeat Vundef 16) (bytes (fst ab), bytes (snd ab)). entailer!.
Qed.

Lemma hhs3_p4_BC_ok {Espec: OracleKind} gv L FR :
  hhs3_p4_pa1_stmt x25519 aead_dec ->
  hhs3_p4_agree_stmt x25519 aead_enc ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p4_SA x25519 aead_enc aead_dec gv L FR) hhs3_p4_BC
    (overridePost (hhs3_p4_SC x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros Hpa1 Hag HH. unfold hhs3_p4_SA, hhs3_Delta, hhs3_R, hhs3_p4_BC. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1. Intros MI nowb PA1 CI1 CI2 Q ok2 M H.
  unfold hhs3_p4_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  destruct CI1 as [[[s1 x1] ck1] y1]. destruct CI2 as [[t2 ck2] h2]. cbv beta iota.
  hhs3_p4_BC_rem (kdf2 ck1 (hhs3_ssb x25519 R)) as K2 HeqK2.
  pose proof HH as (Hx & Ha & _ & _ & _).
  assert (Hnew := Hpa1 _ _ _ _ _ _ _ H0 H4).
  destruct (Hag Hx R L I M1 H1 MI nowb (t2, ck2, h2) Q H0 H3 H7) as (AG1 & AG2 & AG3).
  rewrite <- Hnew in AG1, AG2, AG3. rewrite H5 in AG1. cbn [fst] in AG1.
  assert (Ers: hs_rstatic H = hs_rstatic (p_hs PA1)).
  { pose proof (hhs3_p4_BC_cr_rs (p_hs (hhs3_PA2 PA1)) (s_M0 Q) (s_r Q) (s_idx Q)) as X.
    change (create_response_model x25519 aead_enc (p_hs (hhs3_PA2 PA1)) (s_M0 Q) (s_r Q) (s_idx Q))
      with (hhs3_cr x25519 aead_enc PA1 Q) in X.
    rewrite H5 in X. exact X. }
  assert (Lrs: Zlength (hs_rstatic (p_hs PA1)) = 32).
  { rewrite Hnew. exact (Hx (r_rawa R) basepoint9). }
  rename H4 into Hcin. pose proof Hcin as (_ & _ & Hcs2 & _). cbv beta iota in Hcs2.
  destruct (hhs3_p4_BC_cs2_len _ _ _ _ _ _ _ Hcs2) as (Lck2 & Lh2).
  assert (Lpsk: Zlength (r_psk R) = 32) by (destruct H0 as (_ & _ & X & _); exact X).
  assert_PROP (im_ok (hhs3_M1m x25519 R M1) /\ @field_compatible Noise.CS t_init [] m1) as Him
    by (unfold init_rep; Intros; entailer!).
  destruct Him as [Him FCm1]. assert (Pm1: isptr m1) by (destruct FCm1; auto).
  assert (Leph: Zlength (im_eph M1) = 32) by (destruct Him as (X & _); exact X).
  assert (Ers': hs_rstatic (p_hs (p_set_hs (hhs3_PA2 PA1) H)) = hs_rstatic (p_hs PA1)) by exact Ers.
  (* m_create_response's four input buffers at the one share Ews *)
  rewrite (hhs3_p4_BC_peer_split Tsh (l_pa L)).
  sep_apply (hhs3_p4_BC_rs_open (hs_addr (l_pa L)) (p_hs (p_set_hs (hhs3_PA2 PA1) H))).
  rewrite Ers'.
  sep_apply (hhs3_p4_BC_eph_open Ews m1 (hhs3_M1m x25519 R M1)).
  change (im_eph (hhs3_M1m x25519 R M1)) with (im_eph M1).
  sep_apply (hhs3_p4_BC_shim_open gv S). rewrite H9.
  rewrite (hhs3_p4_BC_tsplit (r_psk R) (l_psk L)).
  sep_apply (hhs3_p4_BC_ci_st Tsh (l_ci L) ck2 h2 (bytes K2) (bytes s1) (bytes t2)).
  unfold hhs3_consts, wg_consts. Intros.
  forward_call (gv, Tsh, l_mr L, Tsh, l_ci L, ck2, h2, Ews, offset_val 8 m1, im_eph M1,
                offset_val 88 (hs_addr (l_pa L)), hs_rstatic (p_hs PA1), l_psk L, r_psk R,
                gv _wg_shim_random_log, s_r Q).
  sep_apply (modus_ponens_wand (hbytes Ews (im_eph M1) (offset_val 8 m1))).
  sep_apply (modus_ponens_wand (hbytes Ews (s_r Q) (gv _wg_shim_random_log))).
  sep_apply (modus_ponens_wand (hbytes Ews (hs_rstatic (p_hs PA1)) (offset_val 88 (hs_addr (l_pa L))))).
  sep_apply (modus_ponens_wand (@data_at HCS Tsh t_mstate (mstate_val ck2 h2) (l_ci L))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p4_BC_tsplit (r_psk R) (l_psk L)))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p4_BC_peer_split Tsh (l_pa L) (p_set_hs (hhs3_PA2 PA1) H)))).
  change (m_create_response_model x25519 aead_enc ck2 h2 (im_eph M1) (hs_rstatic (p_hs PA1)) (r_psk R) (s_r Q))
    with (hhs3_mr x25519 aead_enc R PA1 M1 (t2, ck2, h2) Q).
  assert (HS: forall E encn ep ck h, hhs3_mr x25519 aead_enc R PA1 M1 (t2, ck2, h2) Q = Some (E, encn, ep, ck, h) ->
                ep = clamp (s_r Q) /\ E = x25519 ep basepoint9)
    by (intros E encn ep ck h X; destruct (AG2 E encn ep ck h X) as (_ & X1 & X2); auto).
  sep_apply (hhs3_p4_BC_mr_gen (hhs3_mr x25519 aead_enc R PA1 M1 (t2, ck2, h2) Q) (s_r Q) (l_mr L) HS).
  Intros encv stv.
  match goal with X: match hhs3_mr _ _ _ _ _ _ _ with Some _ => _ | None => True end |- _ => rename X into Hmr end.
  (* CHECK(ok2 == mok) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_if.
    { exfalso. clear - H4 AG1.
      change (m_create_response_model x25519 aead_enc ck2 h2 (im_eph M1) (hs_rstatic (p_hs PA1)) (r_psk R) (s_r Q))
        with (hhs3_mr x25519 aead_enc R PA1 M1 (t2, ck2, h2) Q) in H4.
      rewrite AG1 in H4. destruct (hhs3_mr x25519 aead_enc R PA1 M1 (t2, ck2, h2) Q); vm_compute in H4; discriminate. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* completeness 2: if (all_ok) { .. } *)
  destruct MI as [[[[[Ei encs] enct] epi] cki] hi].
  assert (LMI: Zlength Ei = 32 /\ Zlength epi = 32).
  { destruct H3 as (_ & _ & X & _ & _ & Xr & _). exact (hhs3_p4_BC_mi_len _ _ _ _ _ _ _ _ _ _ _ Hx Xr X). }
  destruct LMI as (LEi & Lepi).
  assert (Lepr: Zlength (clamp (s_r Q)) = 32) by (apply hhs3_p4_BC_clamp_len; exact H7).
  assert (LEr: Zlength (x25519 (clamp (s_r Q)) basepoint9) = 32) by apply Hx.
  assert (LprivA: Zlength (mi_priv (hhs3_IA x25519 R)) = 32).
  { unfold hhs3_IA, mident_of. cbn [mi_priv]. apply hhs3_p4_BC_clamp_len. apply H0. }
  assert (LpubA: Zlength (mi_pub (hhs3_IA x25519 R)) = 32) by apply Hx.
  set (AOK := hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb (Ei, encs, enct, epi, cki, hi)) (Ei, encs, enct, epi, cki, hi) R
                (x25519 (clamp (s_r Q)) basepoint9, [], clamp (s_r Q), [], [])).
  apply <- semax_seq_skip.
  match goal with |- semax _ (PROPx ?P (LOCALx (?a :: ?b :: ?c :: ?d :: _ :: ?Q) (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (a :: b :: c :: d :: temp HC._all_ok (Vint (if AOK then Int.one else Int.zero)) :: Q)
                                (SEPx Rs))) end.
  2: { (* all_ok false *)
    assert (OK3: hhs3_ok3 x25519 R I nowb (Ei, encs, enct, epi, cki, hi) = false)
      by (match goal with X: (if _ then Int.one else _) = Int.zero |- _ => exact (hhs3_p4_BC_if_false _ X) end).
    assert (EA: AOK = false) by (unfold AOK, hhs3_ok4; rewrite OK3; reflexivity).
    forward. rewrite EA, OK3. entailer!. }
  { (* all_ok true *)
    assert (OK3: hhs3_ok3 x25519 R I nowb (Ei, encs, enct, epi, cki, hi) = true)
      by (match goal with X: (if _ then Int.one else _) <> Int.zero |- _ => exact (hhs3_p4_BC_if_true _ X) end).
    assert_PROP (@field_compatible HCS t_mresp [] (l_mr L) /\ @field_compatible HCS t_minit [] (l_mi L) /\
                 @field_compatible HCS t_mident [] (l_ia L)) as FCs by entailer!.
    destruct FCs as (FCmr & FCmi & FCia).
    unfold minit_val.
    rewrite (hhs3_p4_BC_mr_open Tsh (l_mr L) _ _ encv stv FCmr LEr Lepr).
    rewrite (hhs3_p4_BC_mi_open Tsh (l_mi L) Ei epi (bytes encs) (bytes enct) (bytes cki, bytes hi) FCmi LEi Lepi).
    rewrite (hhs3_p4_BC_mident_open Tsh (l_ia L) (hhs3_IA x25519 R) FCia LprivA LpubA).
    repeat flatten_sepcon_in_SEP.
    set (pubA := mi_pub (hhs3_IA x25519 R)) in *.
    set (privA := mi_priv (hhs3_IA x25519 R)) in *.
    set (Er := x25519 (clamp (s_r Q)) basepoint9) in *.
    set (epr := clamp (s_r Q)) in *.
    (* m_dh(d1, mr.eph_priv, mi.ephemeral) *)
    forward_call (Tsh, l_d1b L, Tsh, offset_val 48 (l_mr L), epr, Tsh, l_mi L, Ei).
    hhs3_p4_BC_rem (dh_ok x25519 epr Ei) as a1 Ea1.
    (* && m_dh(d2, mi.eph_priv, mr.ephemeral) *)
    hhs3_p4_BC_fif HC._t'100 (Vint (if (a1 && dh_ok x25519 epi Er)%bool then Int.one else Int.zero))
      (hout Tsh 32 (l_d2b L)) (if a1 then hbytes Tsh (x25519 epi Er) (l_d2b L) else hout Tsh 32 (l_d2b L)).
    { destruct a1; [| contradiction].
      forward_call (Tsh, l_d2b L, Tsh, offset_val 108 (l_mi L), epi, Tsh, l_mr L, Er).
      forward. entailer!. destruct (dh_ok x25519 epi Er); reflexivity. }
    { destruct a1; [discriminate |]. forward. entailer!. }
    hhs3_p4_BC_rem (dh_ok x25519 epi Er) as a2 Ea2.
    (* && bytes_eq(d1, d2, 32) *)
    forward_if (temp HC._t'102 (Vint (if (a1 && a2 && bytes_eqb (x25519 epr Ei) (x25519 epi Er))%bool
                                      then Int.one else Int.zero))).
    { destruct a1; [| contradiction]. destruct a2; [| contradiction].
      change (if true then hbytes Tsh (x25519 epi Er) (l_d2b L) else hout Tsh 32 (l_d2b L))
        with (hbytes Tsh (x25519 epi Er) (l_d2b L)).
      forward_call (Tsh, l_d1b L, x25519 epr Ei, Tsh, l_d2b L, x25519 epi Er).
      { rewrite Hx. entailer!. }
      { rewrite !Hx; rep_lia. }
      forward. entailer!. destruct (bytes_eqb (x25519 epr Ei) (x25519 epi Er)); reflexivity. }
    { forward. entailer!. destruct a1, a2; try reflexivity; discriminate. }
    sep_apply (hhs3_p4_BC_hout32 Tsh (x25519 epr Ei) (l_d1b L) (Hx _ _)).
    sep_apply (hhs3_p4_BC_hif Tsh a1 (x25519 epi Er) (l_d2b L) (Hx _ _)).
    hhs3_p4_BC_rem (bytes_eqb (x25519 epr Ei) (x25519 epi Er)) as b1 Eb1.
    (* && m_dh(d1, mr.eph_priv, ia.pub) *)
    hhs3_p4_BC_fif HC._t'104 (Vint (if (a1 && a2 && b1 && dh_ok x25519 epr pubA)%bool then Int.one else Int.zero))
      (hout Tsh 32 (l_d1b L))
      (if (a1 && a2 && b1)%bool then hbytes Tsh (x25519 epr pubA) (l_d1b L) else hout Tsh 32 (l_d1b L)).
    { destruct (a1 && a2 && b1)%bool; [| contradiction].
      forward_call (Tsh, l_d1b L, Tsh, offset_val 48 (l_mr L), epr, Tsh, offset_val 32 (l_ia L), pubA).
      forward. entailer!. destruct (dh_ok x25519 epr pubA); reflexivity. }
    { destruct (a1 && a2 && b1)%bool; [discriminate |]. forward. entailer!. }
    hhs3_p4_BC_rem (dh_ok x25519 epr pubA) as a3 Ea3.
    (* && m_dh(d2, ia.priv, mr.ephemeral) *)
    hhs3_p4_BC_fif HC._t'106 (Vint (if (a1 && a2 && b1 && a3 && dh_ok x25519 privA Er)%bool then Int.one else Int.zero))
      (hout Tsh 32 (l_d2b L))
      (if (a1 && a2 && b1 && a3)%bool then hbytes Tsh (x25519 privA Er) (l_d2b L) else hout Tsh 32 (l_d2b L)).
    { destruct (a1 && a2 && b1 && a3)%bool; [| contradiction].
      forward_call (Tsh, l_d2b L, Tsh, l_ia L, privA, Tsh, l_mr L, Er).
      forward. entailer!. destruct (dh_ok x25519 privA Er); reflexivity. }
    { destruct (a1 && a2 && b1 && a3)%bool; [discriminate |]. forward. entailer!. }
    hhs3_p4_BC_rem (dh_ok x25519 privA Er) as a4 Ea4.
    (* && bytes_eq(d1, d2, 32) *)
    forward_if (temp HC._t'108 (Vint (if (a1 && a2 && b1 && a3 && a4 &&
                                          bytes_eqb (x25519 epr pubA) (x25519 privA Er))%bool
                                      then Int.one else Int.zero))).
    { destruct (a1 && a2 && b1)%bool; [| contradiction]. destruct a3; [| contradiction]. destruct a4; [| contradiction].
      change (if true then hbytes Tsh (x25519 epr pubA) (l_d1b L) else hout Tsh 32 (l_d1b L))
        with (hbytes Tsh (x25519 epr pubA) (l_d1b L)).
      change (if (true && true)%bool then hbytes Tsh (x25519 privA Er) (l_d2b L) else hout Tsh 32 (l_d2b L))
        with (hbytes Tsh (x25519 privA Er) (l_d2b L)).
      forward_call (Tsh, l_d1b L, x25519 epr pubA, Tsh, l_d2b L, x25519 privA Er).
      { rewrite Hx. entailer!. }
      { rewrite !Hx; rep_lia. }
      forward. entailer!. all: try apply derives_refl.
      destruct (bytes_eqb (x25519 epr pubA) (x25519 privA Er)); reflexivity. }
    { forward. entailer!. destruct (a1 && a2 && b1)%bool, a3, a4; try reflexivity; discriminate. }
    sep_apply (hhs3_p4_BC_hif Tsh (a1 && a2 && b1)%bool (x25519 epr pubA) (l_d1b L) (Hx _ _)).
    sep_apply (hhs3_p4_BC_hif Tsh (a1 && a2 && b1 && a3)%bool (x25519 privA Er) (l_d2b L) (Hx _ _)).
    hhs3_p4_BC_rem (bytes_eqb (x25519 epr pubA) (x25519 privA Er)) as b2 Eb2.
    forward.
    (* all_ok = agree && !bytes_zero(mr.ephemeral, 32) *)
    forward_if (temp HC._t'110 (Vint (if (a1 && a2 && b1 && a3 && a4 && b2 && negb (is_zero Er))%bool
                                      then Int.one else Int.zero))).
    { destruct (a1 && a2 && b1 && a3 && a4 && b2)%bool; [| contradiction].
      forward_call (Tsh, l_mr L, Er).
      { rewrite LEr. entailer!. simpl. destruct (l_mr L); try contradiction. simpl. rewrite ?Ptrofs.add_zero. reflexivity. }
      forward. entailer!. destruct (is_zero Er); reflexivity. }
    { forward. entailer!. destruct (a1 && a2 && b1 && a3 && a4 && b2)%bool; [discriminate | reflexivity]. }
    forward.
    assert (EAOK: AOK = (a1 && a2 && b1 && a3 && a4 && b2 && negb (is_zero Er))%bool).
    { unfold hhs3_p4_BC_hide in Ea1, Ea2, Eb1, Ea3, Ea4, Eb2.
      rewrite Ea1, Ea2, Eb1, Ea3, Ea4, Eb2. unfold AOK, hhs3_ok4. rewrite OK3. reflexivity. }
    rewrite <- EAOK.
    sep_apply (derives_refl' _ _ (eq_sym (hhs3_p4_BC_mr_open Tsh (l_mr L) _ _ encv stv FCmr LEr Lepr))).
    sep_apply (derives_refl' _ _ (eq_sym (hhs3_p4_BC_mi_open Tsh (l_mi L) Ei epi (bytes encs) (bytes enct)
                                            (bytes cki, bytes hi) FCmi LEi Lepi))).
    subst pubA privA.
    sep_apply (derives_refl' _ _ (eq_sym (hhs3_p4_BC_mident_open Tsh (l_ia L) (hhs3_IA x25519 R) FCia LprivA LpubA))).
    forward_if.
    - (* all_ok: CHECK(ok2) *)
      assert (Hok2: ok2 = true).
      { assert (XA: AOK = true)
          by (match goal with X: (if _ then Int.one else _) <> Int.zero |- _ => exact (hhs3_p4_BC_if_true _ X) end).
        rewrite AG1. destruct (hhs3_mr x25519 aead_enc R PA1 M1 (t2, ck2, h2) Q) eqn:EM; [reflexivity |].
        exfalso. pose proof (AG3 eq_refl [] [] []) as X. fold AOK in X. congruence. }
      match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      + apply ENTAIL_refl.
      + forward_if.
        * exfalso. rewrite Hok2 in *.
          match goal with X: typed_true tint (match sem_unary_operation Onotbool tint (Val.of_bool true) with _ => _ end)
            |- _ => vm_compute in X; discriminate X end.
        * forward. entailer!.
      + forward. apply ENTAIL_refl.
      + try unfold POSTCONDITION, abbreviate; try rewrite overridePost_normal'.
        unfold minit_val. entailer!.
    - forward. try unfold POSTCONDITION, abbreviate; try rewrite overridePost_normal'.
      unfold minit_val. entailer!. }
  (* the post SC, by the model's outcome *)
  unfold hhs3_p4_BC_hide in HeqK2.
  unfold hhs3_p4_SC.
  destruct (hhs3_mr x25519 aead_enc R PA1 M1 (t2, ck2, h2) Q) as [[[[[E encn] ep] ck] h]|] eqn:EMR.
  - destruct (HS E encn ep ck h eq_refl) as [Eep EE]. destruct Hmr as [Ee Es]. subst encv stv ok2 ep E.
    assert (P7: hhs3_after_resp x25519 aead_enc R L M1 PA1 (t2, ck2, h2) Q M H
                  (x25519 (clamp (s_r Q)) basepoint9, encn, clamp (s_r Q), ck, h))
      by exact (conj H5 (conj EMR (conj (H8 eq_refl) (conj H6 H7)))).
    assert (P9: AOK = hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb (Ei, encs, enct, epi, cki, hi))
                        (Ei, encs, enct, epi, cki, hi) R
                        (x25519 (clamp (s_r Q)) basepoint9, encn, clamp (s_r Q), ck, h)) by reflexivity.
    Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists (Ei, encs, enct, epi, cki, hi) nowb PA1 (s1, x1, ck1, y1) (t2, ck2, h2).
    Exists Q true M H (x25519 (clamp (s_r Q)) basepoint9, encn, clamp (s_r Q), ck, h) AOK.
    unfold hhs3_p4_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_consts, wg_consts; cbn [app].
    cbv beta iota. rewrite <- HeqK2. unfold mresp_val.
    entailer!.
  - subst ok2.
    sep_apply (@data_at_data_at_ HCS Tsh t_mresp).
    Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists (Ei, encs, enct, epi, cki, hi) nowb PA1 (s1, x1, ck1, y1) (t2, ck2, h2).
    Exists Q false M H (@nil byte, @nil byte, @nil byte, @nil byte, @nil byte) AOK.
    unfold hhs3_p4_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_consts, wg_consts; cbn [app].
    cbv beta iota. rewrite <- HeqK2.
    entailer!.
Qed.

End P4BC.
