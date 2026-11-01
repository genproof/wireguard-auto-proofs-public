(*
   W_cookie_reply and the specifications' compspecs, the shim's boot clock store (shim_core), nondet_bytes' result,
   B's device split into hcy5_drest + its checker, field access to the checker's secret and birthdate).
   Port of the v1 hcy4_p1_lemmas.v. *)
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
Local Open Scope logic.

#[local] Instance hcy5_p1_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p1_cce_C : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p1_cce_H : change_composite_env HCS W_cookie_reply.
Proof. make_cs_preserve HCS W_cookie_reply. Defined.

(* ---------------------------------------------------------------------- *)
(* Conversions of the stack frame                                          *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p1_conv_dev sh p : @data_at_ W_cookie_reply sh t_dev p = @data_at_ Noise.CS sh t_dev p.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_cookie_reply _ sh t_dev eq_refl) p). Qed.
Lemma hcy5_p1_conv_itab sh p : @data_at_ W_cookie_reply sh t_itab p = @data_at_ Noise.CS sh t_itab p.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_cookie_reply _ sh t_itab eq_refl) p). Qed.
Lemma hcy5_p1_conv_ptab sh p : @data_at_ W_cookie_reply sh t_ptab p = @data_at_ Noise.CS sh t_ptab p.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_cookie_reply _ sh t_ptab eq_refl) p). Qed.
Lemma hcy5_p1_conv_skb sh p : @data_at_ W_cookie_reply sh t_skb p = @data_at_ Cookie.CS sh t_skb p.
Proof. symmetry. exact (equal_f (@data_at__change_composite Cookie.CS W_cookie_reply _ sh t_skb eq_refl) p). Qed.
Lemma hcy5_p1_conv_mident sh p : @data_at_ W_cookie_reply sh t_mident p = @data_at_ HCS sh t_mident p.
Proof. symmetry. exact (equal_f (@data_at__change_composite HCS W_cookie_reply _ sh t_mident eq_refl) p). Qed.
Lemma hcy5_p1_conv_bytes sh n p : @data_at_ W_cookie_reply sh (tarray tuchar n) p = hout sh n p.
Proof. unfold hout. apply data_at__tarray_tuchar_cs. Qed.

Lemma hcy5_p1_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_cookie_reply sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros <- HB. unfold hbytes. rewrite Zlength_map. rewrite (@data_at_tarray_tuchar_cs W_cookie_reply HCS). f_equal.
  unfold bytes. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [|exact HB]. intros b Hb.
  unfold Vubyte. rewrite Byte.unsigned_repr by exact Hb. reflexivity.
Qed.

Lemma hcy5_p1_hbytes_free sh bs p : hbytes sh bs p |-- @data_at_ W_cookie_reply sh (tarray tuchar (Zlength bs)) p.
Proof.
  unfold hbytes. rewrite hcy5_p1_conv_bytes. unfold hout. apply data_at_data_at_.
Qed.

(* ---------------------------------------------------------------------- *)
(* The shim: the harness sets the boot clock                               *)
(* ---------------------------------------------------------------------- *)

Definition hcy5_p1_set_boot (S: shim) (now: int64) : shim :=
  mkShim now (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S)
         (s_failnext S) (s_released S) (s_rlallow S).

Lemma hcy5_p1_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hcy5_p1_shim_fold gv S : shim_ok S ->
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))
  |-- shim_core gv S.
Proof. intros H. unfold shim_core. apply andp_right; [apply prop_right; exact H | apply derives_refl]. Qed.

(* ---------------------------------------------------------------------- *)
(* B's device: hcy5_drest and the checker; the checker's fields            *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p1_dev_split sh wg D :
  device_rep sh wg D = hcy5_drest sh wg D * checker_rep sh (cc_addr wg) (d_cc D).
Proof.
  unfold device_rep, hcy5_drest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

Lemma hcy5_p1_fc_cc wg : field_compatible t_dev [] wg -> field_compatible t_cc [] (cc_addr wg).
Proof.
  intros FC. assert (F1: field_compatible t_dev (DOT I._cookie_checker) wg)
    by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  exact F2.
Qed.

Lemma hcy5_p1_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  @field_at W_cookie_reply sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) v wg =
  field_at sh t_cc (DOT I._secret_birthdate) v (cc_addr wg).
Proof.
  intros FC.
  assert (FCW: @field_compatible W_cookie_reply t_dev [] wg).
  { apply (@field_compatible_change_composite Noise.CS W_cookie_reply hcy5_p1_cce_N); [prove_cs_preserve_type | exact FC]. }
  assert (FCc: field_compatible t_cc [] (cc_addr wg)) by (apply hcy5_p1_fc_cc; exact FC).
  rewrite (@field_at_data_at W_cookie_reply). rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset W_cookie_reply)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  rewrite (@field_address_offset Noise.CS)
    by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
  simpl. unfold cc_addr. rewrite offset_offset_val. apply hcy5_p1_tulong_cs.
Qed.

(* the checker: its secret as a byte buffer (offset 0), its birthdate as a field of the device (world),
   the rest *)
Definition hcy5_p1_ccrest (sh: share) (a: val) (CC: checker) : mpred :=
  EX lk: val, field_at sh t_cc (DOT I._cookie_encryption_key) (bytes (cc_ekey CC)) a *
              field_at sh t_cc (DOT I._message_mac1_key) (bytes (cc_mkey CC)) a *
              field_at sh t_cc (DOT I._secret_lock) lk a *
              field_at sh t_cc (DOT I._device) (cc_dev CC) a * spacer sh 108 112 a.

Lemma hcy5_p1_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC =
  !! cc_ok CC &&
  (hbytes sh (cc_secret CC) (cc_addr wg) *
   @field_at W_cookie_reply sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
   hcy5_p1_ccrest sh (cc_addr wg) CC).
Proof.
  intros FC. pose proof (hcy5_p1_fc_cc _ FC) as FCc.
  unfold checker_rep, hcy5_p1_ccrest. rewrite hcy5_p1_cc_birth by exact FC.
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

Lemma hcy5_p1_cc_close sh wg CC : field_compatible t_dev [] wg -> cc_ok CC ->
  hbytes sh (cc_secret CC) (cc_addr wg) *
  @field_at W_cookie_reply sh t_dev (DOT I._cookie_checker DOT I._secret_birthdate) (Vlong (cc_birth CC)) wg *
  hcy5_p1_ccrest sh (cc_addr wg) CC |-- checker_rep sh (cc_addr wg) CC.
Proof.
  intros FC H. rewrite hcy5_p1_cc_open by exact FC.
  apply andp_right; [apply prop_right; exact H | apply derives_refl].
Qed.

End Fields.

(* the rest of the checker does not depend on its secret and birthdate *)
Lemma hcy5_p1_ccrest_eq sh a CC CC' :
  cc_ekey CC = cc_ekey CC' -> cc_mkey CC = cc_mkey CC' -> cc_dev CC = cc_dev CC' ->
  hcy5_p1_ccrest sh a CC = hcy5_p1_ccrest sh a CC'.
Proof. intros E1 E2 E3. unfold hcy5_p1_ccrest. rewrite E1, E2, E3. reflexivity. Qed.

