(* law handshake_receive, B3 kind 0: helpers of segment C (D's device split
   into its checker's secret and the rest; copies of hrx5_B5_lem.v's, renamed). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Local Open Scope logic.

#[local] Instance hrx5_k0c_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_k0c_cce_C : change_composite_env Cookie.CS W.
Proof. make_cs_preserve Cookie.CS W. Defined.

Lemma hrx5_k0c_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Definition hrx5_k0c_drest (sh: share) (wg: val) (D: device) : mpred :=
  !! @field_compatible Noise.CS t_dev [] wg &&
  (@field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg *
   identity_rep sh (id_addr wg) (d_id D) *
   @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   @field_at Noise.CS sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

Lemma hrx5_k0c_dev_split sh wg D :
  device_rep sh wg D = hrx5_k0c_drest sh wg D * checker_rep sh (cc_addr wg) (d_cc D).
Proof.
  unfold device_rep, hrx5_k0c_drest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

Lemma hrx5_k0c_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Lemma hrx5_k0c_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) v wg =
  field_at sh t_cc (DOT I._secret_birthdate) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W hrx5_k0c_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hrx5_k0c_fc_cc; exact FC).
  rewrite (@field_at_data_at W). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hrx5_k0c_tulong_cs.
Qed.

Definition hrx5_k0c_ccrest (sh: share) (a: val) (CC: checker) : mpred :=
  EX lk: val, field_at sh t_cc (DOT I._cookie_encryption_key) (bytes (cc_ekey CC)) a *
              field_at sh t_cc (DOT I._message_mac1_key) (bytes (cc_mkey CC)) a *
              field_at sh t_cc (DOT I._secret_lock) lk a *
              field_at sh t_cc (DOT I._device) (cc_dev CC) a * spacer sh 108 112 a.

Lemma hrx5_k0c_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC =
  !! cc_ok CC &&
  (hbytes sh (cc_secret CC) (cc_addr wg) *
   @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
   hrx5_k0c_ccrest sh (cc_addr wg) CC).
Proof.
  intros FC. pose proof (hrx5_k0c_fc_cc _ FC) as FCc.
  unfold checker_rep, hrx5_k0c_ccrest. rewrite hrx5_k0c_cc_birth by exact FC.
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

Lemma hrx5_k0c_cc_close sh wg CC : field_compatible t_dev [] wg -> cc_ok CC ->
  hbytes sh (cc_secret CC) (cc_addr wg) *
  @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
  hrx5_k0c_ccrest sh (cc_addr wg) CC |-- checker_rep sh (cc_addr wg) CC.
Proof.
  intros FC H. rewrite hrx5_k0c_cc_open by exact FC.
  apply andp_right; [apply prop_right; exact H | apply derives_refl].
Qed.

End Fields.

Lemma hrx5_k0c_b2s_len key m : Zlength (blake2s key 32 m) = 32.
Proof. unfold blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hrx5_k0c_mk1_len x25519 R : Zlength (hrx5_mk1 x25519 R) = 32.
Proof.
  unfold hrx5_mk1, checker_keys. destruct (id_has _); simpl; [unfold label_key; apply hrx5_k0c_b2s_len | reflexivity].
Qed.

Lemma hrx5_k0c_skb_src dv lv proto ip4 ip6 port p :
  0 <= proto <= 65535 -> Zlength ip4 = 4 -> Zlength ip6 = 16 -> Zlength port = 2 ->
  @data_at Cookie.CS Tsh t_skb (dv, (lv, (Vint (Int.repr proto), (bytes ip4, (bytes ip6, bytes port))))) p =
  skb_src_rep Tsh p dv lv (mkSkb nullval Int.zero proto ip4 ip6 port).
Proof.
  intros H1 H2 H3 H4. unfold skb_src_rep, skb_val, skb_ok; simpl.
  rewrite prop_true_andp by auto. reflexivity.
Qed.

Lemma hrx5_k0c_skb_part L dv lv proto ip4 ip6 port :
  skb_src_rep Tsh (l_skb L) dv lv (mkSkb nullval Int.zero proto ip4 ip6 port) |--
  hrx5_skb_part L proto ip4 ip6 port.
Proof.
  unfold skb_src_rep, skb_ok, hrx5_skb_part; simpl. Intros. Exists dv lv. entailer!.
Qed.
