(*
   Ers part and the complement; the harness's identity struct at the world; B's cookie key in the model).
   Adapted from hck3_p1_lemmas (law cookie_mac) and hcy5_p5_a_lemmas. P5. *)
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
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Local Open Scope logic.

#[local] Instance hcy5_p5_b_cce_H : change_composite_env HCS W_cookie_reply.
Proof. make_cs_preserve HCS W_cookie_reply. Defined.

Lemma hcy5_p5_b_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hcy5_p5_b_label_len l p : Zlength (label_key l p) = 32.
Proof. unfold label_key, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hcy5_p5_b_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

(* a Tsh byte buffer as an Ers part (to share one share with a constant) and the rest *)
Lemma hcy5_p5_b_ers_split bs p : hbytes Tsh bs p = hbytes Ers bs p * hbytes (Share.comp Ers) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

(* the harness's identity struct at the world (for main's load of ib.ok) *)
Lemma hcy5_p5_b_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_cookie_reply sh t_mident (mident_val I) p.
Proof.
  assert (E := @data_at_change_composite HCS W_cookie_reply hcy5_p5_b_cce_H sh t_mident (mident_val I) (mident_val I)
           (JMeq_refl _)).
  rewrite E; [reflexivity | prove_cs_preserve_type].
Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

(* the identity without its public key (offset 0) *)
Definition hcy5_p5_b_idrest (sh: share) (a: val) (ID: identity) : mpred :=
  !! field_compatible t_sid [] a &&
  EX lk: val, field_at sh t_sid (DOT I._static_private) (bytes (id_priv ID)) a *
              field_at sh t_sid (DOT I._lock) lk a *
              field_at sh t_sid (DOT I._has_identity) (Val.of_bool (id_has ID)) a * spacer sh 69 72 a.

Lemma hcy5_p5_b_id_open sh a ID :
  identity_rep sh a ID = !! id_ok ID && (hbytes sh (id_pub ID) a * hcy5_p5_b_idrest sh a ID).
Proof.
  unfold identity_rep, hcy5_p5_b_idrest. apply pred_ext.
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

(* the checker without its cookie encryption key (offset 32) *)
Definition hcy5_p5_b_ccrest (sh: share) (a: val) (CC: checker) : mpred :=
  !! field_compatible t_cc [] a &&
  EX lk: val, field_at sh t_cc (DOT I._secret) (bytes (cc_secret CC)) a *
              field_at sh t_cc (DOT I._message_mac1_key) (bytes (cc_mkey CC)) a *
              field_at sh t_cc (DOT I._secret_birthdate) (Vlong (cc_birth CC)) a *
              field_at sh t_cc (DOT I._secret_lock) lk a *
              field_at sh t_cc (DOT I._device) (cc_dev CC) a * spacer sh 108 112 a.

Lemma hcy5_p5_b_cc_open sh a CC :
  checker_rep sh a CC =
  !! cc_ok CC && (hbytes sh (cc_ekey CC) (offset_val 32 a) * hcy5_p5_b_ccrest sh a CC).
Proof.
  unfold checker_rep, hcy5_p5_b_ccrest. apply pred_ext.
  - Intros lk. assert_PROP (field_compatible t_cc [] a) as FCc by entailer!.
    pose proof H as (L1 & L2 & L3).
    unfold hbytes. rewrite L2. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cc _ a).
    rewrite (field_at_data_at sh t_cc (DOT I._cookie_encryption_key)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    Exists lk. entailer!.
  - Intros lk. Exists lk. pose proof H as (L1 & L2 & L3).
    unfold hbytes. rewrite L2. rewrite !(@data_at_tarray_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cc _ a).
    rewrite (field_at_data_at sh t_cc (DOT I._cookie_encryption_key)).
    rewrite !field_address_offset by (destruct H0 as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.

End Fields.

(* the model: B's cookie encryption key (the rotation keeps it) *)
Lemma hcy5_p5_b_ekey x R L Q rr :
  cc_ekey (hcy5_CC2 x R L Q rr) = cc_ekey (hcy5_CC1 x R L).
Proof.
  unfold hcy5_CC2, checker_rotate.
  destruct (birthdate_expired (cc_birth (hcy5_CC1 x R L)) (Int64.repr 120) (q_now Q)); reflexivity.
Qed.

Lemma hcy5_p5_b_ekey_model x R L :
  cc_ekey (hcy5_CC1 x R L) =
  if mi_ok (hcy5_IB x R) then label_key cookie_label (hcy5_pubB x R L) else Zrepeat Byte.zero 32.
Proof.
  unfold hcy5_CC1, hcy5_IB, hcy5_pubB, hcy5_DB, setup_dev, checker_keys. cbn [d_cc cc_ekey d_id].
  change (id_has (setup_identity x (r_rawb R))) with (mi_ok (mident_of x (r_rawb R))).
  destruct (mi_ok (mident_of x (r_rawb R))); reflexivity.
Qed.

Lemma hcy5_p5_b_secret_len x R L Q rr :
  hcy5_run_ok R -> Zlength rr = 32 -> Zlength (cc_secret (hcy5_CC2 x R L Q rr)) = 32.
Proof.
  intros HR Hr. unfold hcy5_CC2, checker_rotate.
  destruct (birthdate_expired (cc_birth (hcy5_CC1 x R L)) (Int64.repr 120) (q_now Q)); cbn [cc_secret].
  - exact Hr.
  - unfold hcy5_CC1. cbn [cc_secret]. apply HR.
Qed.
