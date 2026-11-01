(*
   Ports of cookie_reply's hcy5_p1_lemmas.v and consume_initiation_any's hci5_P1.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Local Open Scope logic.

Notation W := W_handshake_receive.

#[local] Instance hrx5_pa_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_pa_cce_H : change_composite_env HCS W.
Proof. make_cs_preserve HCS W. Defined.

Lemma hrx5_pa_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros <- HB. unfold hbytes. rewrite Zlength_map. rewrite (@data_at_tarray_tuchar_cs W HCS). f_equal.
  unfold bytes. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [|exact HB]. intros b Hb.
  unfold Vubyte. rewrite Byte.unsigned_repr by exact Hb. reflexivity.
Qed.

Lemma hrx5_pa_hbytes_free sh bs p : hbytes sh bs p |-- @data_at_ W sh (tarray tuchar (Zlength bs)) p.
Proof.
  unfold hbytes. rewrite <- (data_at__tarray_tuchar_cs (cs1 := HCS) (cs2 := W)). apply data_at_data_at_.
Qed.

Lemma hrx5_pa_ers_split bs p : hbytes Tsh bs p = hbytes Ers bs p * hbytes (Share.comp Ers) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

(* ---------------------------------------------------------------------- *)
(* The shim: the harness sets the boot clock                               *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_pa_set_boot (S: shim) (now: int64) : shim :=
  mkShim now (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S)
         (s_failnext S) (s_released S) (s_rlallow S).

Lemma hrx5_pa_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Definition hrx5_pa_rest (gv: globals) (S: shim) : mpred :=
  (@data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow)).

Lemma hrx5_pa_core_open gv S :
  shim_core gv S = !! shim_ok S &&
    (@data_at W Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) * hrx5_pa_rest gv S).
Proof.
  unfold shim_core, hrx5_pa_rest. rewrite (@hrx5_pa_tulong_cs Noise.CS W). rewrite !sepcon_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* m_identity: its pub field                                               *)
(* ---------------------------------------------------------------------- *)

Section HCSl.
#[local] Existing Instance HCS.

Definition hrx5_pa_mrest (sh: share) (I: mident) (p: val) : mpred :=
  field_at sh t_mident (DOT HH._priv) (bytes (mi_priv I)) p *
  field_at sh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p.

Lemma hrx5_pa_mident_split sh I p : Zlength (mi_pub I) = 32 ->
  data_at sh t_mident (mident_val I) p |--
  hbytes sh (mi_pub I) (offset_val 32 p) * hrx5_pa_mrest sh I p.
Proof.
  intros Hl. unfold hrx5_pa_mrest, hbytes. rewrite Hl.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT HH._pub)).
  assert_PROP (field_compatible t_mident (DOT HH._pub) p). { entailer!. }
  unfold field_address; rewrite if_true by auto. simpl. cancel.
Qed.

Lemma hrx5_pa_mident_join sh I p : Zlength (mi_pub I) = 32 ->
  hbytes sh (mi_pub I) (offset_val 32 p) * hrx5_pa_mrest sh I p |--
  data_at sh t_mident (mident_val I) p.
Proof.
  intros Hl. unfold hrx5_pa_mrest, hbytes. rewrite Hl.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT HH._pub)).
  assert_PROP (field_compatible t_mident (DOT HH._priv) p). { entailer!. }
  assert (field_compatible t_mident (DOT HH._pub) p).
  { destruct H as (?&?&?&?&?). repeat split; auto. simpl. unfold in_members. simpl. auto. }
  unfold field_address; rewrite if_true by auto. simpl. cancel.
Qed.

End HCSl.

(* the ok field, read by main at the world *)
Lemma hrx5_pa_ok_cs sh (v: val) p :
  @field_at HCS sh t_mident (DOT HH._ok) v p = @field_at W sh t_mident (DOT HH._ok) v p.
Proof.
  unfold field_at. f_equal. f_equal. apply prop_ext. split; intros H.
  - apply (@field_compatible_change_composite HCS W hrx5_pa_cce_H); [prove_cs_preserve_type | exact H].
  - apply (@field_compatible_change_composite HCS W hrx5_pa_cce_H) in H; [exact H | prove_cs_preserve_type].
Qed.

(* ---------------------------------------------------------------------- *)
(* D's device: the rest and the checker; the checker's fields              *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_pa_drest (sh: share) (wg: val) (D: device) : mpred :=
  !! @field_compatible Noise.CS t_dev [] wg &&
  (@field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg *
   identity_rep sh (id_addr wg) (d_id D) *
   @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   @field_at Noise.CS sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

Lemma hrx5_pa_dev_split sh wg D :
  device_rep sh wg D = hrx5_pa_drest sh wg D * checker_rep sh (cc_addr wg) (d_cc D).
Proof.
  unfold device_rep, hrx5_pa_drest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

Lemma hrx5_pa_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Lemma hrx5_pa_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) v wg =
  field_at sh t_cc (DOT I._secret_birthdate) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W hrx5_pa_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hrx5_pa_fc_cc; exact FC).
  rewrite (@field_at_data_at W). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hrx5_pa_tulong_cs.
Qed.

Definition hrx5_pa_ccrest (sh: share) (a: val) (CC: checker) : mpred :=
  EX lk: val, field_at sh t_cc (DOT I._cookie_encryption_key) (bytes (cc_ekey CC)) a *
              field_at sh t_cc (DOT I._message_mac1_key) (bytes (cc_mkey CC)) a *
              field_at sh t_cc (DOT I._secret_lock) lk a *
              field_at sh t_cc (DOT I._device) (cc_dev CC) a * spacer sh 108 112 a.

Lemma hrx5_pa_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC =
  !! cc_ok CC &&
  (hbytes sh (cc_secret CC) (cc_addr wg) *
   @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
   hrx5_pa_ccrest sh (cc_addr wg) CC).
Proof.
  intros FC. pose proof (hrx5_pa_fc_cc _ FC) as FCc.
  unfold checker_rep, hrx5_pa_ccrest. rewrite hrx5_pa_cc_birth by exact FC.
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

Lemma hrx5_pa_cc_close sh wg CC : field_compatible t_dev [] wg -> cc_ok CC ->
  hbytes sh (cc_secret CC) (cc_addr wg) *
  @field_at W sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
  hrx5_pa_ccrest sh (cc_addr wg) CC |-- checker_rep sh (cc_addr wg) CC.
Proof.
  intros FC H. rewrite hrx5_pa_cc_open by exact FC.
  apply andp_right; [apply prop_right; exact H | apply derives_refl].
Qed.

End Fields.

Lemma hrx5_pa_ccrest_eq sh a CC CC' :
  cc_ekey CC = cc_ekey CC' -> cc_mkey CC = cc_mkey CC' -> cc_dev CC = cc_dev CC' ->
  hrx5_pa_ccrest sh a CC = hrx5_pa_ccrest sh a CC'.
Proof. intros E1 E2 E3. unfold hrx5_pa_ccrest. rewrite E1, E2, E3. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* mk1                                                                     *)
(* ---------------------------------------------------------------------- *)

Section Mk1.
Variable x25519: list byte -> list byte -> list byte.

Lemma hrx5_pa_mk1_ok R : mi_ok (hrx5_ID x25519 R) = true ->
  label_key mac1_label (mi_pub (hrx5_ID x25519 R)) = hrx5_mk1 x25519 R.
Proof.
  unfold hrx5_mk1, hrx5_ID, hrx5_sid, setup_identity, checker_keys, identity_of, mident_of. simpl.
  intros E. rewrite E. simpl. apply andb_prop in E. destruct E as [E _]. rewrite E. reflexivity.
Qed.

Lemma hrx5_pa_mk1_nok R : mi_ok (hrx5_ID x25519 R) = false -> Zrepeat Byte.zero 32 = hrx5_mk1 x25519 R.
Proof.
  unfold hrx5_mk1, hrx5_ID, hrx5_sid, setup_identity, checker_keys, identity_of, mident_of. simpl.
  intros E. rewrite E. reflexivity.
Qed.

End Mk1.
