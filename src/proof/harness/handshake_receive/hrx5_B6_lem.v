(* law handshake_receive, main's phase B6: separation-logic helpers.
   - byte buffers: the image split at len - 32 / len - 16 (port of hrx5_body_help's hrx5_help_split2), hin / hout;
   - D's cookie secret inside device_rep (port of hrx5_PA_lem's checker opening), read by bytes_copy;
   - the shim's random log / rate limiter globals inside shim_state4;
   - the queue length global at W (port of hrx5_B2_lem);
   - the snapshot ds: its secret and secret_birthdate fields apart from the rest. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

Notation W := W_handshake_receive.

#[local] Instance hrx5_b6_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_b6_cce_H : change_composite_env HRX W.
Proof. make_cs_preserve HRX W. Defined.
#[local] Instance hrx5_b6_cce_K : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

(* ---------------------------------------------------------------------- *)
(* the snapshot ds                                                         *)
(* ---------------------------------------------------------------------- *)

Section DS.
#[local] Existing Instance W.

Lemma hrx5_b6_ds_cs sh v p : @data_at CKS sh t_devsnap v p = @data_at W sh t_devsnap v p.
Proof.
  rewrite (@data_at_change_composite CKS W _ sh t_devsnap v v (JMeq_refl _)); [reflexivity | prove_cs_preserve_type].
Qed.

End DS.

Section DSK.
#[local] Existing Instance CKS.

(* ds but its secret and secret_birthdate *)
Definition hrx5_b6_dsrest (sh: share) (D: device) (h p: val) : mpred :=
  !! field_compatible t_devsnap [] p &&
  (field_at sh t_devsnap (DOT HC._dev) (d_dev D) p *
   field_at sh t_devsnap (DOT HC._static_public) (bytes (id_pub (d_id D))) p *
   field_at sh t_devsnap (DOT HC._static_private) (bytes (id_priv (d_id D))) p *
   field_at sh t_devsnap (DOT HC._has_identity) (Val.of_bool (id_has (d_id D))) p *
   spacer sh 105 112 p *
   field_at sh t_devsnap (DOT HC._cookie_encryption_key) (bytes (cc_ekey (d_cc D))) p *
   field_at sh t_devsnap (DOT HC._message_mac1_key) (bytes (cc_mkey (d_cc D))) p *
   field_at sh t_devsnap (DOT HC._checker_device) (cc_dev (d_cc D)) p *
   field_at sh t_devsnap (DOT HC._peer_hashtable) (d_ptab D) p *
   field_at sh t_devsnap (DOT HC._index_hashtable) (d_itab D) p *
   field_at sh t_devsnap (DOT HC._peers_head) h p).

Lemma hrx5_b6_ds_open0 sh D h p :
  data_at sh t_devsnap (devsnap_val D h) p =
  field_at sh t_devsnap (DOT HC._secret) (bytes (cc_secret (d_cc D))) p *
  field_at sh t_devsnap (DOT HC._secret_birthdate) (Vlong (cc_birth (d_cc D))) p *
  hrx5_b6_dsrest sh D h p.
Proof.
  unfold hrx5_b6_dsrest. apply pred_ext.
  - assert_PROP (field_compatible t_devsnap [] p) by entailer!.
    unfold_data_at (data_at _ _ _ p). simpl fst; simpl snd. entailer!.
  - Intros. unfold_data_at (data_at _ _ _ p). simpl fst; simpl snd. cancel.
Qed.

Lemma hrx5_b6_sec_fa sh v p : field_compatible t_devsnap [] p ->
  field_at sh t_devsnap (DOT HC._secret) v p = data_at sh (tarray tuchar 32) v (offset_val 73 p).
Proof.
  intros FC. rewrite field_at_data_at.
  rewrite field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  reflexivity.
Qed.

End DSK.

Lemma hrx5_b6_birth_fa sh v p :
  @field_at CKS sh t_devsnap (DOT HC._secret_birthdate) v p =
  @field_at W sh t_devsnap (DOT HM._secret_birthdate) v p.
Proof.
  unfold field_at. f_equal. f_equal. apply prop_ext. split; intros H.
  - apply (@field_compatible_change_composite CKS W hrx5_b6_cce_K); [prove_cs_preserve_type | exact H].
  - apply (@field_compatible_change_composite CKS W hrx5_b6_cce_K) in H; [exact H | prove_cs_preserve_type].
Qed.

Lemma hrx5_b6_ds_open sh D h p :
  @data_at CKS sh t_devsnap (devsnap_val D h) p =
  @data_at CKS sh (tarray tuchar 32) (bytes (cc_secret (d_cc D))) (offset_val 73 p) *
  @field_at W sh t_devsnap (DOT HM._secret_birthdate) (Vlong (cc_birth (d_cc D))) p *
  hrx5_b6_dsrest sh D h p.
Proof.
  rewrite hrx5_b6_ds_open0, <- hrx5_b6_birth_fa. apply pred_ext.
  - unfold hrx5_b6_dsrest. Intros. rewrite hrx5_b6_sec_fa by auto. entailer!.
  - unfold hrx5_b6_dsrest. Intros. rewrite hrx5_b6_sec_fa by auto. entailer!.
Qed.

Lemma hrx5_b6_dsrest_eq sh D CC h p :
  cc_ekey CC = cc_ekey (d_cc D) -> cc_mkey CC = cc_mkey (d_cc D) -> cc_dev CC = cc_dev (d_cc D) ->
  hrx5_b6_dsrest sh (dev_set_cc D CC) h p = hrx5_b6_dsrest sh D h p.
Proof. intros E1 E2 E3. unfold hrx5_b6_dsrest. simpl. rewrite E1, E2, E3. reflexivity. Qed.

(* the device after the packet: D with another checker of the same keys and device, a 32-byte secret *)
Definition hrx5_b6_devok (D D': device) : Prop :=
  exists CC, D' = dev_set_cc D CC /\ cc_ekey CC = cc_ekey (d_cc D) /\ cc_mkey CC = cc_mkey (d_cc D) /\
             cc_dev CC = cc_dev (d_cc D) /\ Zlength (cc_secret CC) = 32.

Lemma hrx5_b6_ds_close sh D D' h p :
  hrx5_b6_devok D D' ->
  @data_at CKS sh (tarray tuchar 32) (bytes (cc_secret (d_cc D'))) (offset_val 73 p) *
  @field_at W sh t_devsnap (DOT HM._secret_birthdate) (Vlong (cc_birth (d_cc D'))) p *
  hrx5_b6_dsrest sh D h p |-- @data_at CKS sh t_devsnap (devsnap_val D' h) p.
Proof.
  intros (CC & -> & E1 & E2 & E3 & _).
  rewrite hrx5_b6_ds_open, hrx5_b6_dsrest_eq by auto. apply derives_refl.
Qed.

(* bytes_copy's destination / source at HCS *)
Lemma hrx5_b6_out_cs sh v p : @data_at CKS sh (tarray tuchar 32) v p |-- hout sh 32 p.
Proof. unfold hout. rewrite <- (@data_at__tarray_tuchar_cs CKS HCS). apply data_at_data_at_. Qed.

Lemma hrx5_b6_in_cs sh bs p : Zlength bs = 32 ->
  hbytes sh bs p = @data_at CKS sh (tarray tuchar 32) (bytes bs) p.
Proof. intros L. unfold hbytes. rewrite L. apply (@data_at_tarray_tuchar_cs HCS CKS). Qed.

Lemma hrx5_b6_hout sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

(* ---------------------------------------------------------------------- *)
(* lengths                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_b6_MAC_len key m : Zlength (MAC key m) = 16.
Proof. unfold MAC, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hrx5_b6_cookie_len K s : Zlength (cookie_of K s) = 16.
Proof. apply hrx5_b6_MAC_len. Qed.

Lemma hrx5_b6_label_len label pub : Zlength (label_key label pub) = 32.
Proof.
  unfold label_key, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
    WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. reflexivity.
Qed.

Lemma hrx5_b6_ckeys_len ID : Zlength (fst (checker_keys ID)) = 32 /\ Zlength (snd (checker_keys ID)) = 32.
Proof. unfold checker_keys. destruct (id_has ID); simpl; rewrite ?hrx5_b6_label_len; split; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the image split (port of hrx5_body_help's hrx5_help_split2)             *)
(* ---------------------------------------------------------------------- *)

Section H.
#[local] Existing Instance HCS.

Lemma hrx5_b6_split2 sh P X p :
  field_compatible (tarray tuchar (Zlength P + Zlength X)) [] p ->
  hbytes sh (P ++ X) p = hbytes sh P p * hbytes sh X (offset_val (Zlength P) p).
Proof.
  intros FC.
  assert (0 <= Zlength P) by apply Zlength_nonneg.
  assert (0 <= Zlength X) by apply Zlength_nonneg.
  unfold hbytes. rewrite Zlength_app.
  rewrite (@split2_data_at_Tarray_tuchar HCS sh (Zlength P + Zlength X) (Zlength P)) by
    (try lia; unfold bytes; rewrite Zlength_map, Zlength_app; lia).
  rewrite field_address0_offset by auto with field_compatible.
  replace (nested_field_offset _ _) with (Zlength P) by (unfold nested_field_offset; simpl; lia).
  replace (Zlength P + Zlength X - Zlength P) with (Zlength X) by lia.
  unfold bytes. rewrite map_app.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite Zlength_map, Z.sub_diag.
  replace (Zlength P + Zlength X - Zlength P) with (Zlength (map Vubyte X)) by (rewrite Zlength_map; lia).
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma hrx5_b6_hin sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. rewrite if_false; auto. Qed.

End H.

(* ---------------------------------------------------------------------- *)
(* the queue length global (port of hrx5_B2_lem)                           *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_b6_qlen gv q :
  qlen_rep gv q = @data_at W Ews tint (Vint q) (gv HM._wg_shim_handshake_queue_len).
Proof.
  unfold qlen_rep.
  rewrite (@data_at_change_composite HRX W _ Ews tint (Vint q) (Vint q)); [reflexivity | apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* ---------------------------------------------------------------------- *)
(* the receive world: D's cookie secret, the shim's log and rate limiter   *)
(* (port of hrx5_PA_lem's checker opening and hrx5_B2_lem's shim split)    *)
(* ---------------------------------------------------------------------- *)

Section Fields.
#[local] Existing Instance Noise.CS.

Lemma hrx5_b6_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Definition hrx5_b6_ccrest (sh: share) (a: val) (CC: checker) : mpred :=
  EX lk: val, field_at sh t_cc (DOT I._cookie_encryption_key) (bytes (cc_ekey CC)) a *
              field_at sh t_cc (DOT I._message_mac1_key) (bytes (cc_mkey CC)) a *
              field_at sh t_cc (DOT I._secret_birthdate) (Vlong (cc_birth CC)) a *
              field_at sh t_cc (DOT I._secret_lock) lk a *
              field_at sh t_cc (DOT I._device) (cc_dev CC) a * spacer sh 108 112 a.

Lemma hrx5_b6_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC =
  !! cc_ok CC && (hbytes sh (cc_secret CC) (cc_addr wg) * hrx5_b6_ccrest sh (cc_addr wg) CC).
Proof.
  intros FC. pose proof (hrx5_b6_fc_cc _ FC) as FCc.
  unfold checker_rep, hrx5_b6_ccrest.
  forget (cc_addr wg) as a.
  apply pred_ext.
  - Intros lk. pose proof H as (L1 & L2 & L3).
    unfold hbytes. rewrite L1. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cc _ a).
    rewrite (field_at_data_at sh t_cc (DOT I._secret)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    Exists lk. entailer!.
  - Intros lk. Exists lk. pose proof H as (L1 & L2 & L3).
    unfold hbytes. rewrite L1. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cc _ a).
    rewrite (field_at_data_at sh t_cc (DOT I._secret)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    entailer!.
Qed.

End Fields.

Lemma hrx5_b6_lend (X Rest P: mpred) : X * Rest |-- P -> X * Rest |-- X * (X -* P).
Proof.
  intros H. apply sepcon_derives; [apply derives_refl |]. apply wand_sepcon_adjoint. rewrite sepcon_comm. exact H.
Qed.

Lemma hrx5_b6_dev_sec sh wg D :
  device_rep sh wg D |--
  hbytes sh (cc_secret (d_cc D)) (cc_addr wg) * (hbytes sh (cc_secret (d_cc D)) (cc_addr wg) -* device_rep sh wg D).
Proof.
  unfold device_rep at 1. Intros. rewrite (hrx5_b6_cc_open sh wg (d_cc D)) by auto. Intros.
  apply derives_trans with (hbytes sh (cc_secret (d_cc D)) (cc_addr wg) *
    (@field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg * identity_rep sh (id_addr wg) (d_id D) *
     hrx5_b6_ccrest sh (cc_addr wg) (d_cc D) *
     @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
     @field_at Noise.CS sh t_dev [StructField I._index_hashtable] (d_itab D) wg)); [cancel |].
  apply hrx5_b6_lend. unfold device_rep. rewrite (hrx5_b6_cc_open sh wg (d_cc D)) by auto. entailer!.
Qed.

Lemma hrx5_b6_rxw_sec (CSw: compspecs) gv sh wg head X :
  rxw_rep CSw gv sh wg head X |--
  hbytes sh (cc_secret (d_cc (rw_D X))) (cc_addr wg) *
  (hbytes sh (cc_secret (d_cc (rw_D X))) (cc_addr wg) -* rxw_rep CSw gv sh wg head X).
Proof.
  unfold rxw_rep at 1. sep_apply (hrx5_b6_dev_sec sh wg (rw_D X)).
  set (A := hbytes sh (cc_secret (d_cc (rw_D X))) (cc_addr wg)).
  set (B := A -* device_rep sh wg (rw_D X)).
  apply derives_trans with (A * (B * itable sh (d_itab (rw_D X)) (rw_T X) * ptable sh (d_ptab (rw_D X)) head *
    peers_rep (rw_PS X) * keypairs_rep CSw (rw_KS X) * shim_state4 gv (rw_S X) (rw_w X) *
    noise_globals gv (rw_kc X) * lul_rep gv (rw_lul X) * rxlog_rep gv (rw_rx X))); [cancel |].
  apply hrx5_b6_lend. unfold rxw_rep. unfold B. sep_apply (modus_ponens_wand A). cancel.
Qed.

Section NS.
#[local] Existing Instance Noise.CS.
(* the shim's globals but the log, the previous log and the rate limiter *)
Definition hrx5_b6_shim_rest (gv: globals) (S: shim) : mpred :=
   data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released).
End NS.

Lemma hrx5_b6_N2W_tbool sh v p : @data_at Noise.CS sh tbool v p = @data_at W sh tbool v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W _ sh tbool v v (JMeq_refl _)); [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_b6_shim_eq gv S w :
  shim_state4 gv S w =
  !! shim_ok S && (hrx5_b6_shim_rest gv S *
     hbytes Ews (s_log S) (gv _wg_shim_random_log) * hbytes Ews (s_logprev S) (gv _wg_shim_random_log_prev) *
     @data_at W Ews tbool (Val.of_bool (s_rlallow S)) (gv HM._wg_shim_ratelimit_allow)) * refwarn4 gv w.
Proof.
  unfold shim_state4, shim_core, hrx5_b6_shim_rest. rewrite (hrx5_b6_N2W_tbool _ _ (gv _wg_shim_ratelimit_allow)).
  apply pred_ext.
  - Intros. pose proof H as (L1 & L2). unfold hbytes. rewrite L1, L2.
    rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS). entailer!.
  - Intros. pose proof H as (L1 & L2). unfold hbytes. rewrite L1, L2.
    rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS). entailer!.
Qed.

Lemma hrx5_b6_rxw_shim (CSw: compspecs) gv sh wg head X :
  rxw_rep CSw gv sh wg head X |--
  (hbytes Ews (s_log (rw_S X)) (gv _wg_shim_random_log) *
   hbytes Ews (s_logprev (rw_S X)) (gv _wg_shim_random_log_prev) *
   @data_at W Ews tbool (Val.of_bool (s_rlallow (rw_S X))) (gv HM._wg_shim_ratelimit_allow)) *
  (hbytes Ews (s_log (rw_S X)) (gv _wg_shim_random_log) *
   hbytes Ews (s_logprev (rw_S X)) (gv _wg_shim_random_log_prev) *
   @data_at W Ews tbool (Val.of_bool (s_rlallow (rw_S X))) (gv HM._wg_shim_ratelimit_allow)
   -* rxw_rep CSw gv sh wg head X).
Proof.
  unfold rxw_rep at 1. rewrite hrx5_b6_shim_eq. Intros.
  set (A := hbytes Ews (s_log (rw_S X)) (gv _wg_shim_random_log) *
   hbytes Ews (s_logprev (rw_S X)) (gv _wg_shim_random_log_prev) *
   @data_at W Ews tbool (Val.of_bool (s_rlallow (rw_S X))) (gv HM._wg_shim_ratelimit_allow)).
  apply derives_trans with (A * (device_rep sh wg (rw_D X) * itable sh (d_itab (rw_D X)) (rw_T X) *
    ptable sh (d_ptab (rw_D X)) head * peers_rep (rw_PS X) * keypairs_rep CSw (rw_KS X) *
    hrx5_b6_shim_rest gv (rw_S X) * refwarn4 gv (rw_w X) *
    noise_globals gv (rw_kc X) * lul_rep gv (rw_lul X) * rxlog_rep gv (rw_rx X))); [unfold A; cancel |].
  apply hrx5_b6_lend. unfold rxw_rep. rewrite hrx5_b6_shim_eq. unfold A. entailer!.
Qed.

(* the queue test q >= 512 *)
Lemma hrx5_b6_lt512 q : Int.signed q >= 512 -> Int.lt q (Int.repr 512) = false.
Proof. intros H. unfold Int.lt. rewrite (Int.signed_repr 512) by rep_lia. destruct (zlt _ _); [lia | reflexivity]. Qed.

Lemma hrx5_b6_lt512' q : Int.signed q < 512 -> Int.lt q (Int.repr 512) = true.
Proof. intros H. unfold Int.lt. rewrite (Int.signed_repr 512) by rep_lia. destruct (zlt _ _); [reflexivity | lia]. Qed.

(* the image at its mac offsets *)
Section H2.
#[local] Existing Instance HCS.

Lemma hrx5_b6_split3 sh msg p : 32 <= Zlength msg -> field_compatible (tarray tuchar (Zlength msg)) [] p ->
  hbytes sh msg p =
  hbytes sh (sublist 0 (Zlength msg - 32) msg) p *
  hbytes sh (sublist (Zlength msg - 32) (Zlength msg - 16) msg) (offset_val (Zlength msg - 32) p) *
  hbytes sh (sublist (Zlength msg - 16) (Zlength msg) msg) (offset_val (Zlength msg - 16) p).
Proof.
  intros Hn FC. set (n := Zlength msg) in *.
  set (P := sublist 0 (n - 32) msg). set (M1 := sublist (n - 32) (n - 16) msg).
  set (M2 := sublist (n - 16) n msg).
  assert (HP: Zlength P = n - 32) by (unfold P; rewrite Zlength_sublist; lia).
  assert (HM1: Zlength M1 = 16) by (unfold M1; rewrite Zlength_sublist; lia).
  assert (HM2: Zlength M2 = 16) by (unfold M2; rewrite Zlength_sublist; lia).
  assert (HI: msg = (P ++ M1) ++ M2) by (unfold P, M1, M2; list_solve).
  rewrite HI at 1.
  rewrite (hrx5_b6_split2 sh (P ++ M1) M2 p)
    by (rewrite !Zlength_app, HP, HM1, HM2; replace (n - 32 + 16 + 16) with n by lia; exact FC).
  rewrite (hrx5_b6_split2 sh P M1 p)
    by (apply field_compatible_array_smaller0 with n; auto; rewrite HP, HM1; lia).
  rewrite Zlength_app, HP, HM1. replace (n - 32 + 16) with (n - 16) by lia. reflexivity.
Qed.

Lemma hrx5_b6_join2 sh msg p : 32 <= Zlength msg -> field_compatible (tarray tuchar (Zlength msg)) [] p ->
  hbytes sh (sublist 0 (Zlength msg - 32) msg) p *
  hbytes sh (sublist (Zlength msg - 32) (Zlength msg - 16) msg) (offset_val (Zlength msg - 32) p) =
  hbytes sh (sublist 0 (Zlength msg - 16) msg) p.
Proof.
  intros Hn FC. set (n := Zlength msg) in *.
  assert (HI: sublist 0 (n - 16) msg = sublist 0 (n - 32) msg ++ sublist (n - 32) (n - 16) msg)
    by (rewrite sublist_rejoin; auto; lia).
  rewrite HI, hrx5_b6_split2.
  - rewrite Zlength_sublist by lia. replace (n - 32 - 0) with (n - 32) by lia. reflexivity.
  - rewrite !Zlength_sublist by lia. apply field_compatible_array_smaller0 with n; auto; lia.
Qed.

End H2.

(* img + len - k *)
Lemma hrx5_b6_offs p n k : isptr p -> 0 <= k <= 64 ->
  force_val (@sem_sub_pi W tuchar Signed (offset_val n p) (Vint (Int.repr k))) = offset_val (n - k) p.
Proof.
  destruct p; try contradiction. intros _ Hk. simpl. f_equal.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.neg_repr, ptrofs_add_repr. f_equal.
Qed.

Lemma hrx5_b6_inteq a b : 0 <= a <= 3 -> 0 <= b <= 3 -> Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros Ha Hb. pose proof (Int.eq_spec (Int.repr a) (Int.repr b)) as E.
  destruct (Int.eq _ _); destruct (Z.eqb_spec a b); auto.
  - apply (f_equal Int.unsigned) in E. rewrite !Int.unsigned_repr in E by rep_lia. contradiction.
  - subst. contradiction.
Qed.
