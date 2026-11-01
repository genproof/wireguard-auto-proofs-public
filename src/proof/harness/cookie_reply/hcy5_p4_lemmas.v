(*
   - B's checker: its secret (offset 0 of cc_addr wb) as hbytes, its birthdate as a field of the device at the
     world W_cookie_reply (main's load of wb.cookie_checker.secret_birthdate, bytes_copy of its secret), and back;
   - the reply: cmsg_rep -> data_at_ (fill_cookie_msg's result is overwritten by message_create);
   - the message buffer: hbytes (HCS) = bytes_at (Noise.CS);
   - the model: message_create_model's checker is the rotation. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Local Open Scope logic.

#[local] Instance hcy5_p4_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.

Lemma hcy5_p4_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hcy5_p4_ptr_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh (tptr t_dev) v p = @data_at cs2 sh (tptr t_dev) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mptr; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mptr) in H2; auto.
Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

Lemma hcy5_p4_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Lemma hcy5_p4_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W_cookie_reply sh t_dev (DOT HY._cookie_checker DOT HY._secret_birthdate) v wg =
  field_at sh t_cc (DOT I._secret_birthdate) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W_cookie_reply t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W_cookie_reply hcy5_p4_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hcy5_p4_fc_cc; exact FC).
  rewrite (@field_at_data_at W_cookie_reply). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W_cookie_reply)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hcy5_p4_tulong_cs.
Qed.

Lemma hcy5_p4_cc_dev sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W_cookie_reply sh t_dev (DOT HY._cookie_checker DOT HY._device) v wg =
  field_at sh t_cc (DOT I._device) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W_cookie_reply t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W_cookie_reply hcy5_p4_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hcy5_p4_fc_cc; exact FC).
  rewrite (@field_at_data_at W_cookie_reply). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W_cookie_reply)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hcy5_p4_ptr_cs.
Qed.

(* the checker but its secret and its birthdate *)
Definition hcy5_p4_ccrest (sh: share) (wg: val) (CC: checker) : mpred :=
  EX lk: val, hbytes sh (cc_ekey CC) (offset_val 32 (cc_addr wg)) *
              hbytes sh (cc_mkey CC) (offset_val 64 (cc_addr wg)) *
              field_at sh t_cc (DOT I._secret_lock) lk (cc_addr wg) * spacer sh 108 112 (cc_addr wg) *
              @field_at W_cookie_reply sh t_dev (DOT HY._cookie_checker DOT HY._device) (cc_dev CC) wg.

(* the checker: its secret as a byte buffer, its birthdate as a field of the device (world), the rest *)
Lemma hcy5_p4_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC =
  !! cc_ok CC &&
  (hbytes sh (cc_secret CC) (cc_addr wg) *
   @field_at W_cookie_reply sh t_dev (DOT HY._cookie_checker DOT HY._secret_birthdate) (Vlong (cc_birth CC)) wg *
   hcy5_p4_ccrest sh wg CC).
Proof.
  intros FC. pose proof (hcy5_p4_fc_cc _ FC) as FCc.
  unfold checker_rep, hcy5_p4_ccrest. rewrite hcy5_p4_cc_birth, hcy5_p4_cc_dev by exact FC.
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

(* the closed checker from its parts *)
Lemma hcy5_p4_cc_close sh wg CC : field_compatible t_dev [] wg -> cc_ok CC ->
  hbytes sh (cc_secret CC) (cc_addr wg) *
  @field_at W_cookie_reply sh t_dev (DOT HY._cookie_checker DOT HY._secret_birthdate) (Vlong (cc_birth CC)) wg *
  hcy5_p4_ccrest sh wg CC
  |-- checker_rep sh (cc_addr wg) CC.
Proof.
  intros FC OK. rewrite (hcy5_p4_cc_open sh wg CC FC). apply andp_right; [apply prop_right; exact OK | apply derives_refl].
Qed.

End Fields.

(* the reply after fill_cookie_msg: overwritten by message_create *)
Lemma hcy5_p4_cmsg_ sh m M : cmsg_rep sh m M |-- @data_at_ Cookie.CS sh t_cmsg m.
Proof. unfold cmsg_rep. Intros. apply data_at_data_at_. Qed.

(* the message buffer: harness's hbytes (HCS) = the protocol's bytes_at (Noise.CS) *)
Lemma hcy5_p4_msg_eq sh bs p : hbytes sh bs p = bytes_at sh bs p.
Proof. unfold hbytes, bytes_at. apply (@data_at_tarray_tuchar_cs HCS Noise.CS). Qed.

(* the address of wb.cookie_checker.secret *)
Lemma hcy5_p4_secret_addr wb : isptr wb ->
  offset_val 0 (cc_addr wb) = cc_addr wb.
Proof. intros. unfold cc_addr. destruct wb; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

(* the model: message_create's checker is the rotation *)
Lemma hcy5_p4_mc_snd xaead_enc CC s index nonce msg S r :
  snd (mc_res xaead_enc CC s index nonce msg S r) = checker_rotate CC (s_boot S) r.
Proof. reflexivity. Qed.

Lemma hcy5_p4_rotate_ok CC now r : cc_ok CC -> Zlength r = 32 -> cc_ok (checker_rotate CC now r).
Proof.
  intros (L1 & L2 & L3) Lr. unfold checker_rotate.
  destruct (birthdate_expired (cc_birth CC) (Int64.repr 120) now); unfold cc_ok; simpl; auto.
Qed.

(* B whole: hcy5_drest and the checker fold into device_rep of hcy5_DBc *)
Lemma hcy5_p4_dev_fold x25519 R L CC :
  hcy5_drest Tsh (l_wb L) (hcy5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC =
  device_rep Tsh (l_wb L) (hcy5_DBc x25519 R L CC).
Proof.
  unfold hcy5_drest, device_rep, hcy5_DBc. simpl.
  apply pred_ext; entailer!.
Qed.

(* the snapshot locals: the world's data_at_ is CKS's *)
#[local] Instance hcy5_p4_cce_KW : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

Lemma hcy5_p4_devsnap_ sh p : @data_at_ W_cookie_reply sh t_devsnap p = @data_at_ CKS sh t_devsnap p.
Proof. symmetry. exact (f_equal (fun f => f p) (@data_at__change_composite CKS W_cookie_reply _ sh t_devsnap eq_refl)). Qed.

Lemma hcy5_p4_skbsnap_ sh p : @data_at_ W_cookie_reply sh t_skbsnap p = @data_at_ CKS sh t_skbsnap p.
Proof. symmetry. exact (f_equal (fun f => f p) (@data_at__change_composite CKS W_cookie_reply _ sh t_skbsnap eq_refl)). Qed.
