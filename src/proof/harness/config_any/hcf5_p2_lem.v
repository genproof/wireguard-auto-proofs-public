(* law config_any: helpers of hcf5_P2_ok.
   The peer split into its handshake and the rest, the device split into its identity and the rest, the
   snapshot hs0's precomputed_static_static field as an output buffer (gfield_ramif), the pure facts. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.
Local Open Scope logic.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

(* the peer without its handshake *)
Definition hcf5_p2_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Lemma hcf5_p2_peer_split sh p P :
  peer_rep sh p P = hs_rep sh (hs_addr p) (p_hs P) * hcf5_p2_prest sh p P.
Proof.
  unfold peer_rep, hcf5_p2_prest. rewrite sepcon_andp_prop.
  f_equal. apply pred_ext; cancel.
Qed.

Lemma hcf5_p2_prest_set sh p P H : hcf5_p2_prest sh p (p_set_hs P H) = hcf5_p2_prest sh p P.
Proof. destruct P; reflexivity. Qed.

Lemma hcf5_p2_peer_join sh p P H :
  hs_rep sh (hs_addr p) H * hcf5_p2_prest sh p P = peer_rep sh p (p_set_hs P H).
Proof. rewrite hcf5_p2_peer_split, hcf5_p2_prest_set. reflexivity. Qed.

(* the device without its identity *)
Definition hcf5_p2_drest (sh: share) (wg: val) (D: device) : mpred :=
  !! field_compatible t_dev [] wg &&
  (field_at sh t_dev [StructField I._dev] (d_dev D) wg *
   checker_rep sh (cc_addr wg) (d_cc D) *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

Lemma hcf5_p2_dev_split sh wg D :
  device_rep sh wg D = identity_rep sh (id_addr wg) (d_id D) * hcf5_p2_drest sh wg D.
Proof.
  unfold device_rep, hcf5_p2_drest. rewrite sepcon_andp_prop.
  f_equal. apply pred_ext; cancel.
Qed.
End NoiseCS.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_p2_pre ID0 RAW PUB :
  precomputed x25519 (identity_of x25519 ID0 RAW) PUB = m_precomputed_model x25519 (mident_of x25519 RAW) PUB.
Proof. reflexivity. Qed.

Lemma hcf5_p2_clamp_len RAW : Zlength RAW = 32 -> Zlength (mi_priv (mident_of x25519 RAW)) = 32.
Proof. intros. simpl. unfold clamp. list_solve. Qed.

Lemma hcf5_p2_mpre_len I PUB : x25519_props x25519 -> Zlength (m_precomputed_model x25519 I PUB) = 32.
Proof.
  intros Hx. unfold m_precomputed_model. destruct (andb _ _); [apply Hx | reflexivity].
Qed.

(* the new peer keeps the invariant *)
Lemma hcf5_p2_inv R L S w D P T KE qin ss :
  hcf5_inv R L S w D P T KE qin -> hcf5_inv R L S w D (p_set_hs P (hs_set_ss (p_hs P) ss)) T KE qin.
Proof.
  unfold hcf5_inv, hcf5_pok, hcf5_slots_ok. destruct P as [? ? ? ? ? [] ? ? ? ? ?]; simpl. tauto.
Qed.

Lemma hcf5_p2_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 ss :
  hcf5_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 ->
  hcf5_same L D (p_set_hs P (hs_set_ss (p_hs P) ss)) T KE S w D0
    (mkSnap (sn_entry sn0) (sn_next sn0) (sn_hashed sn0) (hs_set_ss (sn_hs sn0) ss)) P0 r0 S0 w0 h0.
Proof.
  unfold hcf5_same. intros (Hd & Hs & Hp & Hr & Hsh & Hk & Hh).
  apply hcf5_snap_eqb_eq in Hs. subst sn0 r0.
  repeat split; auto;
    try (unfold hs_snap_cur, snap_of; simpl; apply hcf5_snap_eqb_refl);
    try (rewrite <- Hp; destruct P; reflexivity).
Qed.
End Pure.

(* hs0's precomputed_static_static as an output buffer, and back with the new bytes *)
Definition hcf5_p2_snss (sn: hsnap) (ss: list byte) : hsnap :=
  mkSnap (sn_entry sn) (sn_next sn) (sn_hashed sn) (hs_set_ss (sn_hs sn) ss).

Lemma hcf5_p2_hs0 sh sn p ss :
  @data_at HCS sh t_hsnap (hsnap_val sn) p |--
  @data_at_ HCS sh (tarray tuchar 32)
    (@field_address HCS t_hsnap (DOT WgNoise.harness.x_config_any.code._precomputed_static_static) p) *
  (@data_at HCS sh (tarray tuchar 32) (bytes ss)
     (@field_address HCS t_hsnap (DOT WgNoise.harness.x_config_any.code._precomputed_static_static) p) -*
   @data_at HCS sh t_hsnap (hsnap_val (hcf5_p2_snss sn ss)) p).
Proof.
  assert_PROP (@field_compatible HCS t_hsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans;
    [eapply (gfield_ramif sh t_hsnap [] (StructField WgNoise.harness.x_config_any.code._precomputed_static_static)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - rewrite field_at_data_at. apply sepcon_derives; [apply data_at_data_at_ |].
    apply (allp_left _ (bytes ss)). apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

(* the end of a phase: Sskip into overridePost Q R from an entailment *)
Lemma hcf5_p2_skip {Espec: OracleKind} {cs: compspecs} Delta P Q R :
  ENTAIL Delta, P |-- Q -> semax Delta P Sskip (overridePost Q R).
Proof.
  intros H. eapply semax_pre; [exact H |].
  destruct R as [Rn Rb Rc Rr].
  eapply semax_post; [| | | | apply semax_skip]; simpl; intros;
    apply andp_left2; [apply derives_refl | ..]; apply prop_left; intros [].
Qed.
