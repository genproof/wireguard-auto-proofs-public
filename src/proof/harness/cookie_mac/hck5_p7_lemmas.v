
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Local Open Scope logic.

#[local] Instance hck5_p7_cce_N : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.
#[local] Instance hck5_p7_cce_H : change_composite_env HCS W_cookie_mac.
Proof. make_cs_preserve HCS W_cookie_mac. Defined.

(* the harness sets the boot clock *)
Definition hck5_p7_set_boot (S: shim) (now: int64) : shim :=
  mkShim now (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S)
         (s_failnext S) (s_released S) (s_rlallow S).

Lemma hck5_p7_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_cookie_mac sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p = hbytes sh (map Byte.repr bs) p.
Proof.
  intros <- HB. unfold hbytes. rewrite Zlength_map. rewrite (@data_at_tarray_tuchar_cs W_cookie_mac HCS). f_equal.
  unfold bytes. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [|exact HB]. intros b Hb.
  unfold Vubyte. rewrite Byte.unsigned_repr by exact Hb. reflexivity.
Qed.

Lemma hck5_p7_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hck5_p7_and1 ub : 0 <= ub <= Byte.max_unsigned ->
  Int.and (Int.repr ub) (Int.repr 1) = if Z.odd ub then Int.one else Int.zero.
Proof.
  intros H. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Zmod_odd.
  destruct (Z.odd ub); reflexivity.
Qed.

(* the device without / with its cookie checker *)
Lemma hck5_p7_dev_split sh wg D :
  device_rep sh wg D = hck5_drest sh wg D * checker_rep sh (cc_addr wg) (d_cc D).
Proof.
  unfold device_rep, hck5_drest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

(* the peer without / with its cookie *)
Lemma hck5_p7_peer_split sh p P :
  peer_rep sh p P = hck5_prest sh p P * cookie_rep sh (cookie_addr p) (p_cookie P).
Proof.
  unfold peer_rep, hck5_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

(* a Tsh byte buffer as an Ers part (to share one share with a constant) and the rest *)
Lemma hck5_p7_ers_split bs p : hbytes Tsh bs p = hbytes Ers bs p * hbytes (Share.comp Ers) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

(* the identity without its public key (offset 0) *)
Definition hck5_p7_idrest (sh: share) (a: val) (ID: identity) : mpred :=
  !! field_compatible t_sid [] a &&
  EX lk: val, field_at sh t_sid (DOT I._static_private) (bytes (id_priv ID)) a *
              field_at sh t_sid (DOT I._lock) lk a *
              field_at sh t_sid (DOT I._has_identity) (Val.of_bool (id_has ID)) a * spacer sh 69 72 a.

Lemma hck5_p7_id_open sh a ID :
  identity_rep sh a ID = !! id_ok ID && (hbytes sh (id_pub ID) a * hck5_p7_idrest sh a ID).
Proof.
  unfold identity_rep, hck5_p7_idrest. apply pred_ext.
  - Intros lk. assert_PROP (field_compatible t_sid [] a) as FC by entailer!.
    unfold_data_at (data_at _ t_sid _ a).
    rewrite (field_at_data_at sh t_sid (DOT I._static_public)).
    rewrite field_address_offset by auto with field_compatible. simpl nested_field_type.
    pose proof H as [H1 H2]. unfold hbytes. rewrite H1. rewrite <- (@data_at_tarray_tuchar_cs Noise.CS HCS).
    rewrite isptr_offset_val_zero by auto with field_compatible.
    Exists lk. entailer!.
  - Intros lk. Exists lk. pose proof H as [H1 H2].
    unfold_data_at (data_at _ t_sid _ a).
    rewrite (field_at_data_at sh t_sid (DOT I._static_public)).
    rewrite field_address_offset by auto with field_compatible. simpl nested_field_type.
    unfold hbytes. rewrite H1. rewrite <- (@data_at_tarray_tuchar_cs Noise.CS HCS).
    rewrite isptr_offset_val_zero by auto with field_compatible.
    entailer!.
Qed.

Lemma hck5_p7_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Lemma hck5_p7_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W_cookie_mac sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) v wg =
  field_at sh t_cc (DOT I._secret_birthdate) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W_cookie_mac t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W_cookie_mac hck5_p7_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hck5_p7_fc_cc; exact FC).
  rewrite (@field_at_data_at W_cookie_mac). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W_cookie_mac)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hck5_p7_tulong_cs.
Qed.

Lemma hck5_p7_ptr_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh (tptr t_dev) v p = @data_at cs2 sh (tptr t_dev) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mptr; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mptr) in H2; auto.
Qed.

Lemma hck5_p7_cc_dev sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W_cookie_mac sh t_dev (DOT I._cookie_checker DOT I._device) v wg =
  field_at sh t_cc (DOT I._device) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W_cookie_mac t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W_cookie_mac hck5_p7_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hck5_p7_fc_cc; exact FC).
  rewrite (@field_at_data_at W_cookie_mac). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W_cookie_mac)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hck5_p7_ptr_cs.
Qed.

(* the checker: its three keys as byte buffers, its birthdate and device as fields of the device (world) *)
Definition hck5_p7_ccrest (sh: share) (wg: val) (dev: val) : mpred :=
  EX lk: val, field_at sh t_cc (DOT I._secret_lock) lk (cc_addr wg) * spacer sh 108 112 (cc_addr wg) *
              @field_at W_cookie_mac sh t_dev (DOT I._cookie_checker DOT I._device) dev wg.

Lemma hck5_p7_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC =
  !! cc_ok CC &&
  (hbytes sh (cc_secret CC) (cc_addr wg) * hbytes sh (cc_ekey CC) (offset_val 32 (cc_addr wg)) *
   hbytes sh (cc_mkey CC) (offset_val 64 (cc_addr wg)) *
   @field_at W_cookie_mac sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
   hck5_p7_ccrest sh wg (cc_dev CC)).
Proof.
  intros FC. pose proof (hck5_p7_fc_cc _ FC) as FCc.
  unfold checker_rep, hck5_p7_ccrest. rewrite hck5_p7_cc_birth, hck5_p7_cc_dev by exact FC.
  forget (cc_addr wg) as a.
  apply pred_ext.
  - Intros lk. pose proof H as (L1 & L2 & L3).
    unfold hbytes. rewrite L1, L2, L3. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cc _ a).
    rewrite (field_at_data_at sh t_cc (DOT I._secret)), (field_at_data_at sh t_cc (DOT I._cookie_encryption_key)),
      (field_at_data_at sh t_cc (DOT I._message_mac1_key)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    Exists lk. entailer!.
  - Intros lk. Exists lk. pose proof H as (L1 & L2 & L3).
    unfold hbytes. rewrite L1, L2, L3. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cc _ a).
    rewrite (field_at_data_at sh t_cc (DOT I._secret)), (field_at_data_at sh t_cc (DOT I._cookie_encryption_key)),
      (field_at_data_at sh t_cc (DOT I._message_mac1_key)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    entailer!.
Qed.

(* the cookie: its two keys as byte buffers *)
Definition hck5_p7_ckrest (sh: share) (c: val) (C: cookie) : mpred :=
  !! field_compatible t_cookie [] c &&
  EX lk: val,
  field_at sh t_cookie (DOT I._birthdate) (Vlong (ck_birth C)) c *
  field_at sh t_cookie (DOT I._is_valid) (Val.of_bool (ck_valid C)) c *
  field_at sh t_cookie (DOT I._cookie) (bytes (ck_cookie C)) c *
  field_at sh t_cookie (DOT I._have_sent_mac1) (Val.of_bool (ck_sent C)) c *
  field_at sh t_cookie (DOT I._last_mac1_sent) (bytes (ck_last_mac1 C)) c *
  spacer sh 106 108 c * field_at sh t_cookie (DOT I._lock) lk c.

Lemma hck5_p7_ck_open sh c C :
  cookie_rep sh c C =
  !! cookie_ok C &&
  (hbytes sh (ck_dkey C) (offset_val 42 c) * hbytes sh (ck_mkey C) (offset_val 74 c) * hck5_p7_ckrest sh c C).
Proof.
  unfold cookie_rep, hck5_p7_ckrest, cookie_val. apply pred_ext.
  - Intros lk. pose proof H as (L1 & L2 & L3 & L4).
    assert_PROP (field_compatible t_cookie [] c) as FCc by entailer!.
    unfold hbytes. rewrite L3, L4. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cookie _ c).
    rewrite (field_at_data_at sh t_cookie (DOT I._cookie_decryption_key)),
      (field_at_data_at sh t_cookie (DOT I._message_mac1_key)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    Exists lk. entailer!.
  - Intros lk. Exists lk. pose proof H as (L1 & L2 & L3 & L4).
    unfold hbytes. rewrite L3, L4. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cookie _ c).
    rewrite (field_at_data_at sh t_cookie (DOT I._cookie_decryption_key)),
      (field_at_data_at sh t_cookie (DOT I._message_mac1_key)).
    rewrite !field_address_offset by (destruct H0 as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.
End Fields.

(* the harness's identity struct at the world (for main's load of ib.ok) *)
Lemma hck5_p7_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_cookie_mac sh t_mident (mident_val I) p.
Proof.
  assert (E := @data_at_change_composite HCS W_cookie_mac hck5_p7_cce_H sh t_mident (mident_val I) (mident_val I)
           (JMeq_refl _)).
  rewrite E; [reflexivity | prove_cs_preserve_type].
Qed.

(* pure facts *)
Lemma hck5_p7_label_len l p : Zlength (label_key l p) = 32.
Proof. unfold label_key, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hck5_p7_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hck5_p7_is_zero32 : is_zero zeros32 = true.
Proof. reflexivity. Qed.

Lemma hck5_p7_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.
