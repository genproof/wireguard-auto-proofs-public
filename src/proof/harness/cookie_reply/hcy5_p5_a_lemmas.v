(* Checker part adapted from hcy5_p1_lemmas.v (s4cr-P1), shim part from
   hck3_p7_A2_rot.v (law cookie_mac). P5. *)
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
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.cookie.code.
Local Open Scope logic.

#[local] Instance hcy5_p5_a_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.

Lemma hcy5_p5_a_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hcy5_p5_a_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* B's checker                                                             *)
(* ---------------------------------------------------------------------- *)

Section Fields.
#[local] Existing Instance Noise.CS.

Lemma hcy5_p5_a_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Lemma hcy5_p5_a_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W_cookie_reply sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) v wg =
  field_at sh t_cc (DOT I._secret_birthdate) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W_cookie_reply t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W_cookie_reply hcy5_p5_a_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hcy5_p5_a_fc_cc; exact FC).
  rewrite (@field_at_data_at W_cookie_reply). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W_cookie_reply)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hcy5_p5_a_tulong_cs.
Qed.

(* the checker: its secret as a byte buffer (offset 0), its birthdate as a field of the device (world),
   the rest *)
Definition hcy5_p5_a_ccrest (sh: share) (a: val) (CC: checker) : mpred :=
  EX lk: val, field_at sh t_cc (DOT I._cookie_encryption_key) (bytes (cc_ekey CC)) a *
              field_at sh t_cc (DOT I._message_mac1_key) (bytes (cc_mkey CC)) a *
              field_at sh t_cc (DOT I._secret_lock) lk a *
              field_at sh t_cc (DOT I._device) (cc_dev CC) a * spacer sh 108 112 a.

Lemma hcy5_p5_a_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC =
  !! cc_ok CC &&
  (hbytes sh (cc_secret CC) (cc_addr wg) *
   @field_at W_cookie_reply sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
   hcy5_p5_a_ccrest sh (cc_addr wg) CC).
Proof.
  intros FC. pose proof (hcy5_p5_a_fc_cc _ FC) as FCc.
  unfold checker_rep, hcy5_p5_a_ccrest. rewrite hcy5_p5_a_cc_birth by exact FC.
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

(* hcy5_drest gives the field_compatible of the device *)
Lemma hcy5_p5_a_drest_fc sh wg D : hcy5_drest sh wg D |-- !! @field_compatible Noise.CS t_dev [] wg.
Proof. unfold hcy5_drest. entailer!. Qed.

(* ---------------------------------------------------------------------- *)
(* The shim's random logs                                                  *)
(* ---------------------------------------------------------------------- *)

Section Shim.
#[local] Existing Instance Noise.CS.
(* the shim's globals but the two random logs *)
Definition hcy5_p5_a_shrest (gv: globals) (S: shim) : mpred :=
  (data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic.
End Shim.

Lemma hcy5_p5_a_shim_open gv S w :
  shim_state4 gv S w =
  (!! shim_ok S && (hbytes Ews (s_log S) (gv _wg_shim_random_log) *
                    hbytes Ews (s_logprev S) (gv _wg_shim_random_log_prev) * hcy5_p5_a_shrest gv S *
                    refwarn4 gv w))%logic.
Proof.
  unfold shim_state4, shim_core, hcy5_p5_a_shrest. apply pred_ext.
  - Intros. pose proof H as [H1 H2]. apply andp_right; [apply prop_right; exact H |].
    unfold hbytes. rewrite H1, H2. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS). cancel.
  - Intros. pose proof H as [H1 H2]. apply andp_right; [apply prop_right; exact H |].
    unfold hbytes. rewrite H1, H2. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS). cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* Byte buffers: the first k bytes                                         *)
(* ---------------------------------------------------------------------- *)

Section HCSb.
#[local] Existing Instance HCS.

Lemma hcy5_p5_a_split sh l k p : 0 <= k <= Zlength l ->
  field_compatible (tarray tuchar (Zlength l)) [] p ->
  hbytes sh l p = hbytes sh (sublist 0 k l) p * hbytes sh (sublist k (Zlength l) l) (offset_val k p).
Proof.
  intros Hk FC. unfold hbytes.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength l) k) by (unfold bytes; try rewrite Zlength_map; lia).
  rewrite !Zlength_sublist by lia. unfold bytes. rewrite !sublist_map.
  replace (k - 0) with k by lia.
  rewrite field_address0_offset.
  2: { apply field_compatible_field_compatible0 in FC.
       destruct FC as (?&?&?&?&?); repeat split; auto; simpl; lia. }
  simpl. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma hcy5_p5_a_hbytes_fc sh l p : hbytes sh l p |-- !! field_compatible (tarray tuchar (Zlength l)) [] p.
Proof. unfold hbytes. entailer!. Qed.

End HCSb.

(* ---------------------------------------------------------------------- *)
(* The reply: its nonce (offset 8) and the rest                            *)
(* ---------------------------------------------------------------------- *)

Section CookieCS.
#[local] Existing Instance Cookie.CS.

Definition hcy5_p5_a_cmrest (sh: share) (rp: val) (CM: cookie_msg) : mpred :=
  !! field_compatible t_cmsg [] rp &&
  (field_at sh t_cmsg (DOT WgNoise.cookie.code._header) (Vint (cm_type CM)) rp *
   field_at sh t_cmsg (DOT WgNoise.cookie.code._receiver_index) (Vint (cm_receiver CM)) rp *
   field_at sh t_cmsg (DOT WgNoise.cookie.code._encrypted_cookie) (bytes (cm_enc CM)) rp).

Lemma hcy5_p5_a_cm_open sh rp CM :
  cmsg_rep sh rp CM =
  !! cm_ok CM && (hbytes sh (cm_nonce CM) (offset_val 8 rp) * hcy5_p5_a_cmrest sh rp CM).
Proof.
  unfold cmsg_rep, hcy5_p5_a_cmrest, cmsg_val. apply pred_ext.
  - Intros. pose proof H as (L1 & L2).
    assert_PROP (field_compatible t_cmsg [] rp) as FC by entailer!.
    unfold hbytes. rewrite L1. rewrite !(@data_at_tarray_tuchar_cs HCS Cookie.CS).
    unfold_data_at (data_at _ t_cmsg _ rp).
    rewrite (field_at_data_at sh t_cmsg (DOT WgNoise.cookie.code._nonce)).
    rewrite field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros. pose proof H as (L1 & L2).
    unfold hbytes. rewrite L1. rewrite !(@data_at_tarray_tuchar_cs HCS Cookie.CS).
    unfold_data_at (data_at _ t_cmsg _ rp).
    rewrite (field_at_data_at sh t_cmsg (DOT WgNoise.cookie.code._nonce)).
    rewrite field_address_offset by (destruct H0 as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.

End CookieCS.
