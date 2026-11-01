(* law handshake, phase P5, segment D: helpers of the part cc (pb's handshake ephemeral / timestamp
   as buffers and its last consumption at the world; the snapshot opened the same way; ita opened at pb's
   entry). *)
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
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require WgNoise.harness.x_handshake.code.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_ca_view.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

#[local] Instance hhs3_p5_D_cc_view_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

#[local] Instance hhs3_p5_D_cc_view_CCEH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

#[local] Instance hhs3_p5_D_cc_view_CCHW : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

Local Open Scope logic.

Lemma hhs3_p5_D_cc_view_lic sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr)
    [StructField HC._last_initiation_consumption; StructField HC._handshake] (Vlong v) p.
Proof.
  intros H.
  change [StructField HC._last_initiation_consumption; StructField HC._handshake]
    with ([StructField HC._last_initiation_consumption] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._last_initiation_consumption]
             [StructField HC._handshake] (Vlong v) (Vlong v) p (JMeq_refl _)).
  rewrite hhs3_p5_D_ca_view_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p5_D_cc_view_CCE sh t_hs
           [StructField prot_repr3.I._last_initiation_consumption] (Vlong v) (Vlong v) (JMeq_refl _)
           hhs3_p5_D_ca_view_hscs)).
Qed.

Lemma hhs3_p5_D_cc_view_eph sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._ephemeral_private] (bytes l) (hs_addr p) =
  hbytes sh l (offset_val 104 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p5_D_ca_view_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hhs3_p5_D_cc_view_ts sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 12 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._latest_timestamp] (bytes l) (hs_addr p) =
  hbytes sh l (offset_val 328 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p5_D_ca_view_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

(* the peer without the handshake's ephemeral, timestamp, last consumption *)
Definition hhs3_p5_D_cc_view_other (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint (hs_state H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._static_identity] (hs_sid H) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_ephemeral] (bytes (hs_reph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._preshared_key] (bytes (hs_psk H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._hash] (bytes (hs_hash H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._chaining_key] (bytes (hs_ck H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Definition hhs3_p5_D_cc_view (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in
  (hbytes sh (hs_eph H) (offset_val 104 p) * hbytes sh (hs_ts H) (offset_val 328 p) *
   @field_at W_handshake sh (Tstruct HC._wg_peer noattr)
     [StructField HC._last_initiation_consumption; StructField HC._handshake] (Vlong (hs_lic H)) p *
   hhs3_p5_D_cc_view_other sh p P).

Lemma hhs3_p5_D_cc_view_eq sh p P :
  peer_rep sh p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) && hhs3_p5_D_cc_view sh p P.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (Le & _ & _ & _ & _ & _ & _ & Lt).
    apply andp_right; [apply prop_right; split; auto |].
    unfold hhs3_p5_D_cc_view, hhs3_p5_D_cc_view_other. cbv zeta.
    rewrite <- (hhs3_p5_D_cc_view_eph sh p _ Hfc Le), <- (hhs3_p5_D_cc_view_ts sh p _ Hfc Lt),
      <- (hhs3_p5_D_cc_view_lic sh p _ Hfc).
    Intros lk. Exists lk. cancel.
  - Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (Le & _ & _ & _ & _ & _ & _ & Lt).
    unfold hhs3_p5_D_cc_view, hhs3_p5_D_cc_view_other. cbv zeta.
    rewrite <- (hhs3_p5_D_cc_view_eph sh p _ Hfc Le), <- (hhs3_p5_D_cc_view_ts sh p _ Hfc Lt),
      <- (hhs3_p5_D_cc_view_lic sh p _ Hfc).
    unfold peer_rep. Intros lk.
    apply andp_right; [apply prop_right; auto |].
    unfold hs_rep. rewrite (prop_true_andp (hs_ok (p_hs P))) by exact Hok.
    Exists lk. cancel.
Qed.

(* the snapshot: ephemeral and timestamp as buffers, last consumption and index at the world *)
Definition hhs3_p5_D_cc_view_srest (sh: share) (s: val) (sn: hsnap) : mpred :=
  let E := sn_entry sn in let H := sn_hs sn in
  (@field_at HCS sh t_hsnap (DOT HC._peer) (e_peer E) s *
   @field_at HCS sh t_hsnap (DOT HC._next) (sn_next sn) s *
   @field_at HCS sh t_hsnap (DOT HC._hashed) (Val.of_bool (sn_hashed sn)) s * spacer sh 17 20 s *
   @field_at HCS sh t_hsnap (DOT HC._type) (Vint (e_type E)) s *
   @field_at HCS sh t_hsnap (DOT HC._state) (Vint (hs_state H)) s *
   @field_at HCS sh t_hsnap (DOT HC._static_identity) (hs_sid H) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_static) (bytes (hs_rstatic H)) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_ephemeral) (bytes (hs_reph H)) s *
   @field_at HCS sh t_hsnap (DOT HC._precomputed_static_static) (bytes (hs_ss H)) s *
   @field_at HCS sh t_hsnap (DOT HC._preshared_key) (bytes (hs_psk H)) s *
   @field_at HCS sh t_hsnap (DOT HC._hash) (bytes (hs_hash H)) s *
   @field_at HCS sh t_hsnap (DOT HC._chaining_key) (bytes (hs_ck H)) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex H)) s).

Lemma hhs3_p5_D_cc_view_snap sh s sn :
  @field_compatible HCS t_hsnap [] s -> Zlength (hs_eph (sn_hs sn)) = 32 -> Zlength (hs_ts (sn_hs sn)) = 12 ->
  @data_at HCS sh t_hsnap (hsnap_val sn) s =
  hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 s) * hbytes sh (hs_ts (sn_hs sn)) (offset_val 272 s) *
  @field_at W_handshake sh t_hsnap (DOT HC._last_initiation_consumption) (Vlong (hs_lic (sn_hs sn))) s *
  @field_at W_handshake sh t_hsnap (DOT HC._index) (Vint (e_index (sn_entry sn))) s *
  hhs3_p5_D_cc_view_srest sh s sn.
Proof.
  intros FC Le Lt. unfold hhs3_p5_D_cc_view_srest, hsnap_val, hbytes. rewrite Le, Lt.
  unfold_data_at (@data_at HCS sh t_hsnap _ s).
  rewrite (@field_at_data_at HCS sh t_hsnap (DOT HC._ephemeral_private)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._latest_timestamp)).
  rewrite !(@field_address_offset HCS) by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite <- (f_equal (fun f => f s) (@field_at_change_composite HCS W_handshake hhs3_p5_D_cc_view_CCHW sh t_hsnap
           (DOT HC._last_initiation_consumption) (Vlong (hs_lic (sn_hs sn))) (Vlong (hs_lic (sn_hs sn))) (JMeq_refl _)
           ltac:(vm_compute; reflexivity))).
  rewrite <- (f_equal (fun f => f s) (@field_at_change_composite HCS W_handshake hhs3_p5_D_cc_view_CCHW sh t_hsnap
           (DOT HC._index) (Vint (e_index (sn_entry sn))) (Vint (e_index (sn_entry sn))) (JMeq_refl _)
           ltac:(vm_compute; reflexivity))).
  apply pred_ext; cancel.
Qed.

(* the table after create_initiation *)
Lemma hhs3_p5_D_cc_view_TA1 L I : hhs3_TA1 L I =
  mkT [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I))] [hs_addr (l_pb L)].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, t_entry, t_upd, hhs3_TA0, hhs3_EB; cbn [t_D t_L sfind supd vremove].
  rewrite !if_true by auto. reflexivity.
Qed.

(* the table opened at its only entry: the entry as a field of the peer, at the world *)
Lemma hhs3_p5_D_cc_view_open tab pb E : @field_compatible Noise.CS t_peer [] pb ->
  itable Tsh tab (mkT [(hs_addr pb, Tsh, E)] [hs_addr pb]) =
  @data_at Noise.CS Tsh t_itab (hs_addr pb) tab *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (e_peer E, (nullval, (Vtrue, (Vint (e_type E), Vint (e_index E))))) pb.
Proof.
  intros FC0. assert (FC: @field_compatible W_handshake t_peer [] pb).
  { apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FC0]. }
  unfold itable, pool_item_rep, entry_at, entry_val, vin. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon succ_in].
  rewrite if_true by auto. destruct (in_dec eq_dec (hs_addr pb) [hs_addr pb]) as [_|N]; [|exfalso; apply N; left; auto].
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  erewrite <- (@data_at_change_composite Noise.CS W_handshake _ Tsh t_entry_s); [| apply JMeq_refl | prove_cs_preserve_type].
  rewrite prop_true_andp.
  2:{ unfold itable_wf; cbn [t_L t_D saddrs map]. split; [constructor; [intros []|constructor]|].
      split; [intros x Hx; exact Hx|]. split; [constructor; [intros []|constructor]|].
      constructor; [apply writable_share_top | constructor]. }
  rewrite sepcon_emp. reflexivity.
Qed.

Lemma hhs3_p5_D_cc_view_open1 L I : @field_compatible Noise.CS t_peer [] (l_pb L) ->
  itable Tsh (l_ita L) (hhs3_TA1 L I) =
  @data_at Noise.CS Tsh t_itab (hs_addr (l_pb L)) (l_ita L) *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (l_pb L, (nullval, (Vtrue, (Vint IDX_HANDSHAKE, Vint (i_idx I))))) (l_pb L).
Proof. intros FC. rewrite hhs3_p5_D_cc_view_TA1. apply (hhs3_p5_D_cc_view_open _ _ (mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I)) FC). Qed.

(* pb's handshake after consume_response vs the snapshot *)
Lemma hhs3_p5_D_cc_view_new x25519 R L I M1 H1 M2 ST2 :
  let H := p_hs (p_set_refs (hhs3_p5_new x25519 R L M1 H1 M2 ST2) Int.one) in
  let sn := hhs3_p5_snap x25519 R L I M1 H1 in
  hs_eph H = hs_eph (sn_hs sn) /\ hs_ts H = hs_ts (sn_hs sn) /\ hs_lic H = hs_lic (sn_hs sn) /\
  e_index (sn_entry sn) = i_idx I.
Proof. destruct ST2. repeat split; reflexivity. Qed.
