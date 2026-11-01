(* law handshake, phase P3, segment D: helpers of the part cc (pa's handshake ephemeral as a buffer;
   the snapshot's ephemeral as a buffer, its hashed / index at the world; itb opened at pa's entry, which is
   in the pool but not hashed).  Adapted from hhs3_p5_D_ca_view.v / hhs3_p5_D_cc_view.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

#[local] Instance hhs3_p3_D_cc_view_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

#[local] Instance hhs3_p3_D_cc_view_CCEH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

#[local] Instance hhs3_p3_D_cc_view_CCHW :change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

Local Open Scope logic.

Lemma hhs3_p3_D_cc_view_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hhs3_p3_D_cc_view_fc_hs p f : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible Noise.CS t_peer [StructField f; StructField prot_repr3.I._handshake] p ->
  @field_compatible Noise.CS t_hs [StructField f] (hs_addr p).
Proof.
  intros H H1. apply (field_compatible_app [StructField f] t_peer [StructField prot_repr3.I._handshake]) in H1.
  rewrite field_address_offset in H1 by auto with field_compatible. exact H1.
Qed.

Lemma hhs3_p3_D_cc_view_eph sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._ephemeral_private] (bytes l) (hs_addr p) =
  hbytes sh l (offset_val 104 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p3_D_cc_view_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

(* the peer without the handshake's ephemeral *)
Definition hhs3_p3_D_cc_view_other (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint (hs_state H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._static_identity] (hs_sid H) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_ephemeral] (bytes (hs_reph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._preshared_key] (bytes (hs_psk H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._hash] (bytes (hs_hash H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._chaining_key] (bytes (hs_ck H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._latest_timestamp] (bytes (hs_ts H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Definition hhs3_p3_D_cc_view (sh: share) (p: val) (P: peer) : mpred :=
  hbytes sh (hs_eph (p_hs P)) (offset_val 104 p) * hhs3_p3_D_cc_view_other sh p P.

Lemma hhs3_p3_D_cc_view_eq sh p P :
  peer_rep sh p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) && hhs3_p3_D_cc_view sh p P.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (Le & _).
    apply andp_right; [apply prop_right; split; auto |].
    unfold hhs3_p3_D_cc_view, hhs3_p3_D_cc_view_other. cbv zeta.
    rewrite <- (hhs3_p3_D_cc_view_eph sh p _ Hfc Le).
    Intros lk. Exists lk. cancel.
  - Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (Le & _).
    unfold hhs3_p3_D_cc_view, hhs3_p3_D_cc_view_other. cbv zeta.
    rewrite <- (hhs3_p3_D_cc_view_eph sh p _ Hfc Le).
    unfold peer_rep. Intros lk.
    apply andp_right; [apply prop_right; auto |].
    unfold hs_rep. rewrite (prop_true_andp (hs_ok (p_hs P))) by exact Hok.
    Exists lk. cancel.
Qed.

(* the snapshot: ephemeral as a buffer, hashed and index at the world *)
Definition hhs3_p3_D_cc_view_srest (sh: share) (s: val) (sn: hsnap) : mpred :=
  let E := sn_entry sn in let H := sn_hs sn in
  (@field_at HCS sh t_hsnap (DOT HC._peer) (e_peer E) s *
   @field_at HCS sh t_hsnap (DOT HC._next) (sn_next sn) s * spacer sh 17 20 s *
   @field_at HCS sh t_hsnap (DOT HC._type) (Vint (e_type E)) s *
   @field_at HCS sh t_hsnap (DOT HC._state) (Vint (hs_state H)) s *
   @field_at HCS sh t_hsnap (DOT HC._last_initiation_consumption) (Vlong (hs_lic H)) s *
   @field_at HCS sh t_hsnap (DOT HC._static_identity) (hs_sid H) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_static) (bytes (hs_rstatic H)) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_ephemeral) (bytes (hs_reph H)) s *
   @field_at HCS sh t_hsnap (DOT HC._precomputed_static_static) (bytes (hs_ss H)) s *
   @field_at HCS sh t_hsnap (DOT HC._preshared_key) (bytes (hs_psk H)) s *
   @field_at HCS sh t_hsnap (DOT HC._hash) (bytes (hs_hash H)) s *
   @field_at HCS sh t_hsnap (DOT HC._chaining_key) (bytes (hs_ck H)) s *
   @field_at HCS sh t_hsnap (DOT HC._latest_timestamp) (bytes (hs_ts H)) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex H)) s).

Lemma hhs3_p3_D_cc_view_snap sh s sn :
  @field_compatible HCS t_hsnap [] s -> Zlength (hs_eph (sn_hs sn)) = 32 ->
  @data_at HCS sh t_hsnap (hsnap_val sn) s =
  hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 s) *
  @field_at W_handshake sh t_hsnap (DOT HC._hashed) (Val.of_bool (sn_hashed sn)) s *
  @field_at W_handshake sh t_hsnap (DOT HC._index) (Vint (e_index (sn_entry sn))) s *
  hhs3_p3_D_cc_view_srest sh s sn.
Proof.
  intros FC Le. unfold hhs3_p3_D_cc_view_srest, hsnap_val, hbytes. rewrite Le.
  unfold_data_at (@data_at HCS sh t_hsnap _ s).
  rewrite (@field_at_data_at HCS sh t_hsnap (DOT HC._ephemeral_private)).
  rewrite !(@field_address_offset HCS) by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite <- (f_equal (fun f => f s) (@field_at_change_composite HCS W_handshake hhs3_p3_D_cc_view_CCHW sh t_hsnap
           (DOT HC._hashed) (Val.of_bool (sn_hashed sn)) (Val.of_bool (sn_hashed sn)) (JMeq_refl _)
           ltac:(vm_compute; reflexivity))).
  rewrite <- (f_equal (fun f => f s) (@field_at_change_composite HCS W_handshake hhs3_p3_D_cc_view_CCHW sh t_hsnap
           (DOT HC._index) (Vint (e_index (sn_entry sn))) (Vint (e_index (sn_entry sn))) (JMeq_refl _)
           ltac:(vm_compute; reflexivity))).
  apply pred_ext; cancel.
Qed.

(* the table with one entry in its pool, not hashed: the entry as a field of the peer, at the world *)
Lemma hhs3_p3_D_cc_view_open tab pa E : @field_compatible Noise.CS t_peer [] pa ->
  itable Tsh tab (mkT [(hs_addr pa, Tsh, E)] []) =
  @data_at Noise.CS Tsh t_itab nullval tab *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (e_peer E, (nullval, (Val.of_bool false, (Vint (e_type E), Vint (e_index E))))) pa.
Proof.
  intros FC0. assert (FC: @field_compatible W_handshake t_peer [] pa).
  { apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FC0]. }
  unfold itable, pool_item_rep, entry_at, entry_val, vin. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon succ_in].
  destruct (in_dec eq_dec (hs_addr pa) []) as [N|_]; [destruct N|].
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  erewrite <- (@data_at_change_composite Noise.CS W_handshake _ Tsh t_entry_s); [| apply JMeq_refl | prove_cs_preserve_type].
  rewrite prop_true_andp.
  2:{ unfold itable_wf; cbn [t_L t_D saddrs map]. split; [constructor|].
      split; [intros x Hx; destruct Hx|]. split; [constructor; [intros []|constructor]|].
      constructor; [apply writable_share_top | constructor]. }
  rewrite sepcon_emp. reflexivity.
Qed.

Lemma hhs3_p3_D_cc_view_open1 L : @field_compatible Noise.CS t_peer [] (l_pa L) ->
  itable Tsh (l_itb L) (hhs3_TB0 L) =
  @data_at Noise.CS Tsh t_itab nullval (l_itb L) *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (l_pa L, (nullval, (Val.of_bool false, (Vint IDX_HANDSHAKE, Vint Int.zero)))) (l_pa L).
Proof. intros FC. apply (hhs3_p3_D_cc_view_open _ _ (hhs3_EA L) FC). Qed.

(* pa's handshake after consume_initiation (one reference again) vs the snapshot *)
Lemma hhs3_p3_D_cc_view_new x25519 R L M1 nowb CI2 :
  let H := p_hs (hhs3_PA2 (hhs3_p3_new x25519 R L M1 nowb CI2)) in
  let sn := hhs3_p3_snap x25519 R L in
  hs_eph H = hs_eph (sn_hs sn) /\ sn_hashed sn = false /\ e_index (sn_entry sn) = Int.zero.
Proof. destruct CI2 as [[t ck] h]. repeat split; reflexivity. Qed.
