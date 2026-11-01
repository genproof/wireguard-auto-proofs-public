(* law handshake, phase P3, segment B.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
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

Local Open Scope logic.

Lemma hhs3_p3_B_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

Lemma hhs3_p3_B_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

#[local] Instance hhs3_p3_B_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

#[local] Instance hhs3_p3_B_CCEH : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

(* the initiation message: its three byte fields as buffers, the rest *)
Section NoiseFields.
#[local] Existing Instance Noise.CS.

Definition hhs3_p3_B_irest (sh: share) (m: val) (M: init_msg) : mpred :=
  field_at sh t_init (DOT I._header) (Vint (im_type M)) m *
  field_at sh t_init (DOT I._sender_index) (Vint (im_sender M)) m *
  field_at sh t_init (DOT I._macs) (bytes (im_mac1 M), bytes (im_mac2 M)) m.

Lemma hhs3_p3_B_init_open sh m M :
  init_rep sh m M =
  !! (im_ok M /\ field_compatible t_init [] m) &&
  (hbytes sh (im_eph M) (offset_val 8 m) * hbytes sh (im_encs M) (offset_val 40 m) *
   hbytes sh (im_enct M) (offset_val 88 m) * hhs3_p3_B_irest sh m M).
Proof.
  unfold init_rep, hhs3_p3_B_irest, init_val. apply pred_ext.
  - Intros. pose proof H as (L1 & L2 & L3 & L4 & L5).
    assert_PROP (field_compatible t_init [] m) as FC by entailer!.
    unfold hbytes. rewrite L1, L2, L3. rewrite !(@hhs3_p3_B_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_init _ m).
    rewrite (field_at_data_at sh t_init (DOT I._unencrypted_ephemeral)),
      (field_at_data_at sh t_init (DOT I._encrypted_static)),
      (field_at_data_at sh t_init (DOT I._encrypted_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros. rename H into Hok, H0 into FC. pose proof Hok as (L1 & L2 & L3 & L4 & L5).
    unfold hbytes. rewrite L1, L2, L3. rewrite !(@hhs3_p3_B_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_init _ m).
    rewrite (field_at_data_at sh t_init (DOT I._unencrypted_ephemeral)),
      (field_at_data_at sh t_init (DOT I._encrypted_static)),
      (field_at_data_at sh t_init (DOT I._encrypted_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.
End NoiseFields.
(* the peer: its handshake apart; the handshake: eight byte buffers, three scalars, the rest *)
Section NoiseHs.
#[local] Existing Instance Noise.CS.

Definition hhs3_p3_B_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Lemma hhs3_p3_B_peer_split sh p P :
  peer_rep sh p P = hhs3_p3_B_prest sh p P * hs_rep sh (hs_addr p) (p_hs P).
Proof.
  unfold peer_rep, hhs3_p3_B_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Definition hhs3_p3_B_hrest (sh: share) (h: val) (H: handshake) : mpred :=
  field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
  (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h.

Definition hhs3_p3_B_hbufs (sh: share) (h: val) (H: handshake) : mpred :=
  hbytes sh (hs_eph H) (offset_val 56 h) * hbytes sh (hs_rstatic H) (offset_val 88 h) *
  hbytes sh (hs_reph H) (offset_val 120 h) * hbytes sh (hs_ss H) (offset_val 152 h) *
  hbytes sh (hs_psk H) (offset_val 184 h) * hbytes sh (hs_hash H) (offset_val 216 h) *
  hbytes sh (hs_ck H) (offset_val 248 h) * hbytes sh (hs_ts H) (offset_val 280 h).

Lemma hhs3_p3_B_hs_open sh h H :
  hs_rep sh h H =
  !! (hs_ok H /\ field_compatible t_hs [] h) &&
  (hhs3_p3_B_hbufs sh h H *
   field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h *
   field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   hhs3_p3_B_hrest sh h H).
Proof.
  unfold hs_rep, hhs3_p3_B_hrest, hhs3_p3_B_hbufs. apply pred_ext.
  - Intros lk. pose proof H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    assert_PROP (field_compatible t_hs (DOT I._state) h) as FC0 by entailer!.
    assert (FC: field_compatible t_hs [] h) by (destruct FC0 as (?&?&?&?&?); repeat split; auto).
    unfold hbytes. rewrite L1, L2, L3, L4, L5, L6, L7, L8. rewrite !(@hhs3_p3_B_tuchar_cs HCS Noise.CS).
    rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
      (field_at_data_at sh t_hs (DOT I._remote_static)),
      (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
      (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
      (field_at_data_at sh t_hs (DOT I._preshared_key)),
      (field_at_data_at sh t_hs (DOT I._hash)),
      (field_at_data_at sh t_hs (DOT I._chaining_key)),
      (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    Exists lk. entailer!.
  - Intros lk. rename H0 into Hok, H1 into FC. pose proof Hok as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    unfold hbytes. rewrite L1, L2, L3, L4, L5, L6, L7, L8. rewrite !(@hhs3_p3_B_tuchar_cs HCS Noise.CS).
    rewrite (field_at_data_at sh t_hs (DOT I._ephemeral_private)),
      (field_at_data_at sh t_hs (DOT I._remote_static)),
      (field_at_data_at sh t_hs (DOT I._remote_ephemeral)),
      (field_at_data_at sh t_hs (DOT I._precomputed_static_static)),
      (field_at_data_at sh t_hs (DOT I._preshared_key)),
      (field_at_data_at sh t_hs (DOT I._hash)),
      (field_at_data_at sh t_hs (DOT I._chaining_key)),
      (field_at_data_at sh t_hs (DOT I._latest_timestamp)).
    rewrite !field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    Exists lk. entailer!.
Qed.
End NoiseHs.

Lemma hhs3_p3_B_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_handshake (Tstruct HC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_handshake hhs3_p3_B_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hhs3_p3_B_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_handshake (Tstruct HC._wg_peer noattr) [StructField HC._handshake] p = hs_addr p.
Proof. intros H. apply hhs3_p3_B_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

(* the snapshot: five byte buffers, two scalars at the world, the rest *)
Definition hhs3_p3_B_snrest (sh: share) (p: val) (s: hsnap) : mpred :=
  let E := sn_entry s in let H := sn_hs s in
  @field_at HCS sh t_hsnap (DOT HC._peer) (e_peer E) p *
  @field_at HCS sh t_hsnap (DOT HC._next) (sn_next s) p *
  @field_at HCS sh t_hsnap (DOT HC._hashed) (Val.of_bool (sn_hashed s)) p *
  @field_at HCS sh t_hsnap (DOT HC._type) (Vint (e_type E)) p *
  @field_at HCS sh t_hsnap (DOT HC._index) (Vint (e_index E)) p *
  @field_at HCS sh t_hsnap (DOT HC._state) (Vint (hs_state H)) p *
  @field_at HCS sh t_hsnap (DOT HC._static_identity) (hs_sid H) p *
  @field_at HCS sh t_hsnap (DOT HC._ephemeral_private) (bytes (hs_eph H)) p *
  @field_at HCS sh t_hsnap (DOT HC._hash) (bytes (hs_hash H)) p *
  @field_at HCS sh t_hsnap (DOT HC._chaining_key) (bytes (hs_ck H)) p *
  spacer sh 17 20 p.

Lemma hhs3_p3_B_sncs : cs_preserve_type HCS W_handshake (@coeq _ _ hhs3_p3_B_CCEH) t_hsnap = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3_p3_B_snap_open sh p s :
  @field_compatible HCS t_hsnap [] p ->
  Zlength (hs_rstatic (sn_hs s)) = 32 -> Zlength (hs_reph (sn_hs s)) = 32 -> Zlength (hs_ss (sn_hs s)) = 32 ->
  Zlength (hs_psk (sn_hs s)) = 32 -> Zlength (hs_ts (sn_hs s)) = 12 ->
  @data_at HCS sh t_hsnap (hsnap_val s) p =
  hbytes sh (hs_rstatic (sn_hs s)) (offset_val 80 p) * hbytes sh (hs_reph (sn_hs s)) (offset_val 112 p) *
  hbytes sh (hs_ss (sn_hs s)) (offset_val 144 p) * hbytes sh (hs_psk (sn_hs s)) (offset_val 176 p) *
  hbytes sh (hs_ts (sn_hs s)) (offset_val 272 p) *
  @field_at W_handshake sh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex (sn_hs s))) p *
  @field_at W_handshake sh t_hsnap (DOT HC._last_initiation_consumption) (Vlong (hs_lic (sn_hs s))) p *
  hhs3_p3_B_snrest sh p s.
Proof.
  intros FC L2 L3 L4 L5 L8.
  (* unfold_data_at takes 64 s here; the same steps by hand take 2 s *)
  pose proof (@field_at_Tstruct HCS sh t_hsnap [] HH._hs_snap noattr (hsnap_val s) (hsnap_val s) p eq_refl
                (JMeq_refl _)) as HT.
  simpl co_members in HT. lazy beta iota zeta delta [nested_sfieldlist_at] in HT.
  simpl in HT. unfold withspacer in HT. simpl in HT. unfold hsnap_val in HT. simpl in HT.
  unfold hsnap_val, hhs3_p3_B_snrest, hbytes. rewrite L2, L3, L4, L5, L8.
  unfold data_at at 1. rewrite HT. clear HT.
  rewrite (@field_at_data_at HCS sh t_hsnap (DOT HC._remote_static)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._remote_ephemeral)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._precomputed_static_static)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._preshared_key)),
    (@field_at_data_at HCS sh t_hsnap (DOT HC._latest_timestamp)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite <- (@field_at_change_composite HCS W_handshake hhs3_p3_B_CCEH sh t_hsnap (DOT HC._remote_index)
               (Vint (hs_rindex (sn_hs s))) (Vint (hs_rindex (sn_hs s))) (JMeq_refl _) hhs3_p3_B_sncs).
  rewrite <- (@field_at_change_composite HCS W_handshake hhs3_p3_B_CCEH sh t_hsnap (DOT HC._last_initiation_consumption)
               (Vlong (hs_lic (sn_hs s))) (Vlong (hs_lic (sn_hs s))) (JMeq_refl _) hhs3_p3_B_sncs).
  apply pred_ext; cancel.
Qed.

(* ci's spub and ts fields as byte buffers *)
Lemma hhs3_p3_B_ci_spub sh p ck h keyv sp tsv :
  @field_compatible HCS t_mcinit [] p -> Zlength sp = 32 ->
  @data_at HCS sh t_mcinit (mcinit_val ck h keyv (bytes sp) tsv) p =
  hbytes sh sp (offset_val 96 p) *
  (@field_at HCS sh t_mcinit (DOT HC._st) (bytes ck, bytes h) p *
   @field_at HCS sh t_mcinit (DOT HC._key) keyv p *
   @field_at HCS sh t_mcinit (DOT HC._ts) tsv p).
Proof.
  intros FC L1. unfold mcinit_val, hbytes. rewrite L1.
  unfold_data_at (@data_at HCS sh t_mcinit _ p).
  rewrite (@field_at_data_at HCS sh t_mcinit (DOT HC._spub)).
  rewrite field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  apply pred_ext; cancel.
Qed.

Lemma hhs3_p3_B_ci_ts sh p ck h keyv spv t :
  @field_compatible HCS t_mcinit [] p -> Zlength t = 12 ->
  @data_at HCS sh t_mcinit (mcinit_val ck h keyv spv (bytes t)) p =
  hbytes sh t (offset_val 128 p) *
  (@field_at HCS sh t_mcinit (DOT HC._st) (bytes ck, bytes h) p *
   @field_at HCS sh t_mcinit (DOT HC._key) keyv p *
   @field_at HCS sh t_mcinit (DOT HC._spub) spv p).
Proof.
  intros FC L1. unfold mcinit_val, hbytes. rewrite L1.
  unfold_data_at (@data_at HCS sh t_mcinit _ p).
  rewrite (@field_at_data_at HCS sh t_mcinit (DOT HC._ts)).
  rewrite field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  apply pred_ext; cancel.
Qed.

Lemma hhs3_p3_B_ci_undef p :
  @data_at_ HCS Tsh t_mcinit p =
  @data_at HCS Tsh t_mcinit ((Zrepeat Vundef 32, Zrepeat Vundef 32), (Zrepeat Vundef 32, (Zrepeat Vundef 32, Zrepeat Vundef 12))) p.
Proof. reflexivity. Qed.

Lemma hhs3_p3_B_tsplit bs p : hbytes Tsh bs p = hbytes Ews bs p * hbytes (Share.comp Ews) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

Lemma hhs3_p3_B_clamp_len r : Zlength r = 32 -> Zlength (clamp r) = 32.
Proof. intros. unfold clamp. list_solve. Qed.

Lemma hhs3_p3_B_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_handshake sh t_mident (mident_val I) p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite HCS W_handshake hhs3_p3_B_CCEH sh t_mident (mident_val I)
    (mident_val I) (@JMeq_refl _ (mident_val I)) ltac:(vm_compute; reflexivity))).
Qed.

Lemma hhs3_p3_B_b2s_len key m : Zlength (model.blake2s key 32 m) = 32.
Proof. unfold model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hhs3_p3_B_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac, HASH. apply hhs3_p3_B_b2s_len. Qed.

Lemma hhs3_p3_B_wand_eq (P Q C: mpred) (X: Prop) : P = !!X && (Q * C) -> P |-- Q * (Q -* P).
Proof.
  intros E. rewrite E at 1. Intros. cancel. apply wand_sepcon_adjoint. rewrite E. entailer!.
Qed.

(* the remote static of a handshake, with a wand back *)
Lemma hhs3_p3_B_rs_open sh h H :
  hs_rep sh h H |-- hbytes sh (hs_rstatic H) (offset_val 88 h) *
                   (hbytes sh (hs_rstatic H) (offset_val 88 h) -* hs_rep sh h H).
Proof.
  apply (hhs3_p3_B_wand_eq _ _
    (hbytes sh (hs_eph H) (offset_val 56 h) *
     hbytes sh (hs_reph H) (offset_val 120 h) * hbytes sh (hs_ss H) (offset_val 152 h) *
     hbytes sh (hs_psk H) (offset_val 184 h) * hbytes sh (hs_hash H) (offset_val 216 h) *
     hbytes sh (hs_ck H) (offset_val 248 h) * hbytes sh (hs_ts H) (offset_val 280 h) *
     @field_at Noise.CS sh t_hs [StructField I._state] (Vint (hs_state H)) h *
     @field_at Noise.CS sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
     @field_at Noise.CS sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
     hhs3_p3_B_hrest sh h H)
    (hs_ok H /\ @field_compatible Noise.CS t_hs [] h)).
  rewrite hhs3_p3_B_hs_open. unfold hhs3_p3_B_hbufs. f_equal. apply pred_ext; cancel.
Qed.

Local Open Scope Z_scope.

Section P3B.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_B_cs1_len I eph encs s key ck h :
  aead_props aead_enc aead_dec -> Zlength encs = 48 ->
  m_consume_init1_model x25519 aead_dec I eph encs = Some (s, key, ck, h) ->
  Zlength s = 32 /\ Zlength key = 32 /\ Zlength ck = 32 /\ Zlength h = 32.
Proof.
  intros HA HL E. unfold m_consume_init1_model, consume_init_stage1 in E. cbn [im_eph im_encs id_priv id_pub] in E.
  destruct (negb _); [discriminate |].
  destruct (aead_dec _ _ _ _) as [s'|] eqn:Ed; [| discriminate].
  injection E as <- <- <- <-. apply (aead_dec_length _ _ HA) in Ed. rewrite HL in Ed.
  unfold kdf1, kdf2, mix_hash, HASH. rewrite !hhs3_p3_B_hmac_len, hhs3_p3_B_b2s_len. lia.
Qed.

Lemma hhs3_p3_B_cs2_len ss ck h enct t ck2 h2 :
  aead_props aead_enc aead_dec -> Zlength enct = 28 ->
  m_consume_init2_model aead_dec ss ck h enct = Some (t, ck2, h2) ->
  Zlength t = 12 /\ Zlength ck2 = 32 /\ Zlength h2 = 32.
Proof.
  intros HA HL E. unfold m_consume_init2_model, consume_init_stage2 in E. cbn [im_enct] in E.
  destruct (negb _); [discriminate |].
  destruct (aead_dec _ _ _ _) as [t'|] eqn:Ed; [| discriminate].
  injection E as <- <- <-. apply (aead_dec_length _ _ HA) in Ed. rewrite HL in Ed.
  unfold kdf1, mix_hash, HASH. rewrite !hhs3_p3_B_hmac_len, hhs3_p3_B_b2s_len. lia.
Qed.

Ltac hhs3_p3_B_absurd :=
  first [ discriminate
        | exfalso; match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end
        | exfalso; match goal with Hx: Int.repr ?a = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia; discriminate end
        | exfalso; match goal with Hx: @eq int _ _ |- _ =>
            apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end ].

Ltac hhs3_p3_B_fchain := repeat (apply semax_if_seq; forward_if; [hhs3_p3_B_absurd | forward]).

Ltac hhs3_p3_B_close R S m1 m2 a0 f0 l0 I M1 H1 MI nowb Cin acc CI1 CI2 :=
  unfold hhs3_p3_SB, hhs3_p3_SBC;
  Exists R S m1 m2 a0 f0 l0 I M1 H1; Exists MI nowb Cin acc; Exists CI1 CI2;
  unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_consts, wg_consts; cbn [app];
  rewrite hhs3_p3_B_init_open.

Lemma hhs3_p3_B_ok {Espec: OracleKind} gv L FR :
  hhs3_p3_acc_stmt x25519 aead_dec ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p3_SA x25519 aead_enc aead_dec gv L FR) hhs3_p3_B
    (overridePost (hhs3_p3_SB x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HAcc HH. unfold hhs3_p3_SA, hhs3_Delta, hhs3_R, hhs3_p3_B. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1. Intros MI nowb Cin.
  unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  rewrite (hhs3_p3_B_mident_W Tsh (hhs3_IB x25519 R) (l_ib L)).
  forward.
  rewrite <- (hhs3_p3_B_mident_W Tsh (hhs3_IB x25519 R) (l_ib L)).
  unfold mident_val at 1. cbv beta iota.
  pose proof HH as (Hx & Ha & _ & _ & _).
  destruct (mi_ok (hhs3_IB x25519 R)) eqn:EB.
  2: { apply semax_if_seq. forward_if. { hhs3_p3_B_absurd. } forward.
       hhs3_p3_B_fchain. forward.
       assert (Eacc: hhs3_p3_acc x25519 aead_dec R L M1 nowb = false) by (unfold hhs3_p3_acc; rewrite EB; reflexivity).
       unfold hhs3_p3_SB, hhs3_p3_SBC.
       Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists MI nowb Cin false.
       Exists (@nil byte, @nil byte, @nil byte, @nil byte) (@nil byte, @nil byte, @nil byte).
       unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
       entailer!. }
  (* B has an identity: stage 1 *)
  apply semax_if_seq. forward_if. 2: { hhs3_p3_B_absurd. }
  rewrite hhs3_p3_B_init_open. Intros.
  match goal with Hm: im_ok _ |- _ => pose proof Hm as (Le & Ls & Lt & _ & _) end.
  rewrite hhs3_p3_B_ci_undef.
  assert (LprivB: Zlength (mi_priv (hhs3_IB x25519 R)) = 32).
  { unfold hhs3_IB, mident_of. cbn [mi_priv]. apply hhs3_p3_B_clamp_len. apply H. }
  assert (LpubB: Zlength (mi_pub (hhs3_IB x25519 R)) = 32) by apply Hx.
  unfold hhs3_consts, wg_consts. Intros.
  apply -> seq_assoc. eapply semax_seq'.
  forward_call (gv, Tsh, l_ci L, Zrepeat Vundef 12, Tsh, l_ib L, hhs3_IB x25519 R, Ews, offset_val 8 m1,
                im_eph (hhs3_M1m x25519 R M1), offset_val 40 m1, im_encs (hhs3_M1m x25519 R M1)).
  1: { assert (isptr m1) by (destruct H8; auto). tauto. }
  change (m_consume_init1_model x25519 aead_dec (hhs3_IB x25519 R) (im_eph (hhs3_M1m x25519 R M1))
            (im_encs (hhs3_M1m x25519 R M1))) with (hhs3_cs1 x25519 aead_dec R M1).
  apply ENTAIL_refl.
  unfold MORE_COMMANDS, abbreviate. forward.
  destruct (hhs3_cs1 x25519 aead_dec R M1) as [[[[s key] ck] h]|] eqn:E1.
  2: { cbv beta iota. hhs3_p3_B_fchain. forward.
       assert (Eacc: hhs3_p3_acc x25519 aead_dec R L M1 nowb = false)
         by (unfold hhs3_p3_acc; rewrite EB, E1; reflexivity).
       hhs3_p3_B_close R S m1 m2 a0 f0 l0 I M1 H1 MI nowb Cin false
         (@nil byte, @nil byte, @nil byte, @nil byte) (@nil byte, @nil byte, @nil byte).
       entailer!. }
  (* stage 1 succeeded: spub == pa's remote static *)
  destruct (hhs3_p3_B_cs1_len _ _ _ s key ck h Ha Ls E1) as (Lsp & Lkey & Lck & Lh).
  apply semax_if_seq. forward_if. 2: { hhs3_p3_B_absurd. }
  assert_PROP (@field_compatible HCS t_mcinit [] (l_ci L)) as FCci by entailer!.
  rewrite (hhs3_p3_B_ci_spub Tsh (l_ci L) ck h (bytes key) s (Zrepeat Vundef 12) FCci Lsp).
  assert (Ers: hs_rstatic (p_hs (hhs3_p3_pa x25519 R L Cin)) = hs_rstatic (p_hs (hhs3_PA0 x25519 R L))).
  { destruct Cin as [[a P]|]; [| reflexivity].
    destruct (proj2 (proj2 (HAcc R L M1 nowb H)) a P H5) as [_ Hr]. exact Hr. }
  assert (LrsA: Zlength (hs_rstatic (p_hs (hhs3_PA0 x25519 R L))) = 32) by apply Hx.
  rewrite (hhs3_p3_B_peer_split Tsh (l_pa L)).
  sep_apply (hhs3_p3_B_rs_open Tsh (hs_addr (l_pa L)) (p_hs (hhs3_p3_pa x25519 R L Cin))).
  rewrite Ers. flatten_sepcon_in_SEP.
  apply -> seq_assoc. eapply semax_seq'.
  forward_call (Tsh, offset_val 96 (l_ci L), s, Tsh, offset_val 88 (hs_addr (l_pa L)),
                hs_rstatic (p_hs (hhs3_PA0 x25519 R L))).
  { entailer!. simpl. unfold hs_addr. rewrite ?offset_offset_val, Lsp. reflexivity. }
  apply ENTAIL_refl.
  unfold MORE_COMMANDS, abbreviate. forward.
  sep_apply (modus_ponens_wand (hbytes Tsh (hs_rstatic (p_hs (hhs3_PA0 x25519 R L))) (offset_val 88 (hs_addr (l_pa L))))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p3_B_peer_split Tsh (l_pa L) (hhs3_p3_pa x25519 R L Cin)))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p3_B_ci_spub Tsh (l_ci L) ck h (bytes key) s (Zrepeat Vundef 12) FCci Lsp))).
  destruct (bytes_eqb s (hs_rstatic (p_hs (hhs3_PA0 x25519 R L)))) eqn:E2.
  2: { hhs3_p3_B_fchain. forward.
       assert (Eacc: hhs3_p3_acc x25519 aead_dec R L M1 nowb = false)
         by (unfold hhs3_p3_acc; rewrite EB, E1, E2; reflexivity).
       sep_apply (@data_at_data_at_ HCS Tsh t_mcinit).
       hhs3_p3_B_close R S m1 m2 a0 f0 l0 I M1 H1 MI nowb Cin false
         (@nil byte, @nil byte, @nil byte, @nil byte) (@nil byte, @nil byte, @nil byte).
       entailer!. }
  (* stage 2 *)
  apply semax_if_seq. forward_if. 2: { hhs3_p3_B_absurd. }
  assert (Lssb: Zlength (hhs3_ssb x25519 R) = 32).
  { unfold hhs3_ssb, m_precomputed_model. match goal with |- context [if ?b then _ else _] => destruct b end; [apply Hx | reflexivity]. }
  rewrite (hhs3_p3_B_tsplit (hhs3_ssb x25519 R)). flatten_sepcon_in_SEP.
  apply -> seq_assoc. eapply semax_seq'.
  forward_call (gv, Tsh, l_ci L, ck, h, bytes key, bytes s, Zrepeat Vundef 12, Ews, l_ssb L, hhs3_ssb x25519 R,
                offset_val 88 m1, im_enct (hhs3_M1m x25519 R M1)).
  1: { destruct H8; auto. }
  1: { unfold bytes. rewrite !Zlength_map. auto. }
  change (m_consume_init2_model aead_dec (hhs3_ssb x25519 R) ck h (im_enct (hhs3_M1m x25519 R M1)))
    with (hhs3_p3_cs2 x25519 aead_dec R M1 (s, key, ck, h)).
  apply ENTAIL_refl.
  unfold MORE_COMMANDS, abbreviate. forward.
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p3_B_tsplit (hhs3_ssb x25519 R) (l_ssb L)))).
  destruct (hhs3_p3_cs2 x25519 aead_dec R M1 (s, key, ck, h)) as [[[t ck2] h2]|] eqn:E3.
  2: { cbv beta iota. hhs3_p3_B_fchain. forward.
       assert (Eacc: hhs3_p3_acc x25519 aead_dec R L M1 nowb = false)
         by (unfold hhs3_p3_acc; rewrite EB, E1; cbn beta iota zeta; rewrite E2, E3; reflexivity).
       hhs3_p3_B_close R S m1 m2 a0 f0 l0 I M1 H1 MI nowb Cin false
         (@nil byte, @nil byte, @nil byte, @nil byte) (@nil byte, @nil byte, @nil byte).
       entailer!. }
  (* stage 2 succeeded: the timestamp newer than the snapshot's *)
  destruct (hhs3_p3_B_cs2_len (hhs3_ssb x25519 R) ck h (im_enct M1) t ck2 h2 Ha Lt E3) as (Lt12 & Lck2 & Lh2).
  apply semax_if_seq. forward_if. 2: { hhs3_p3_B_absurd. }
  assert_PROP (@field_compatible HCS t_hsnap [] (l_snap L)) as FCsn by entailer!.
  assert (L2: Zlength (hs_rstatic (sn_hs (hhs3_p3_snap x25519 R L))) = 32) by exact (Hx (r_rawa R) basepoint9).
  assert (L3: Zlength (hs_reph (sn_hs (hhs3_p3_snap x25519 R L))) = 32) by reflexivity.
  assert (L4: Zlength (hs_ss (sn_hs (hhs3_p3_snap x25519 R L))) = 32).
  { change (hs_ss (sn_hs (hhs3_p3_snap x25519 R L)))
      with (precomputed x25519 (d_id (hhs3_DB x25519 R L)) (mi_pub (hhs3_IA x25519 R))).
    unfold precomputed. match goal with |- context [if ?b then _ else _] => destruct b end; [apply Hx | reflexivity]. }
  assert (L5: Zlength (hs_psk (sn_hs (hhs3_p3_snap x25519 R L))) = 32) by (destruct H as (_ & _ & Lp & _); exact Lp).
  assert (L8: Zlength (hs_ts (sn_hs (hhs3_p3_snap x25519 R L))) = 12) by reflexivity.
  rewrite (hhs3_p3_B_ci_ts Tsh (l_ci L) ck2 h2 (bytes (kdf2 ck (hhs3_ssb x25519 R))) (bytes s) t FCci Lt12).
  rewrite (hhs3_p3_B_snap_open Tsh (l_snap L) (hhs3_p3_snap x25519 R L) FCsn L2 L3 L4 L5 L8).
  remember (hs_ts (sn_hs (hhs3_p3_snap x25519 R L))) as T0 eqn:ET0.
  apply -> seq_assoc.
  repeat flatten_sepcon_in_SEP.
  (* the frame cancellation of this call does not terminate on the whole SEP: freeze it *)
  freeze FZ := - (hbytes Tsh t (offset_val 128 (l_ci L))) (hbytes Tsh T0 (offset_val 272 (l_snap L))).
  eapply semax_seq'.
  forward_call (Tsh, offset_val 128 (l_ci L), t, Tsh, offset_val 272 (l_snap L), T0).
  apply ENTAIL_refl.
  unfold MORE_COMMANDS, abbreviate. forward.
  thaw FZ.
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p3_B_ci_ts Tsh (l_ci L) ck2 h2 (bytes (kdf2 ck (hhs3_ssb x25519 R))) (bytes s) t FCci Lt12))).
  destruct (ts_newer t T0) eqn:E4.
  2: { subst T0.
       sep_apply (derives_refl' _ _ (eq_sym (hhs3_p3_B_snap_open Tsh (l_snap L) (hhs3_p3_snap x25519 R L) FCsn L2 L3 L4 L5 L8))).
       change (hs_ts (sn_hs (hhs3_p3_snap x25519 R L))) with (hs_ts (p_hs (hhs3_PA0 x25519 R L))) in E4.
       hhs3_p3_B_fchain. forward.
       assert (Eacc: hhs3_p3_acc x25519 aead_dec R L M1 nowb = false)
         by (unfold hhs3_p3_acc; rewrite EB, E1; cbn beta iota zeta; rewrite E2, E3; cbn beta iota zeta; rewrite E4; reflexivity).
       sep_apply (@data_at_data_at_ HCS Tsh t_mcinit).
       hhs3_p3_B_close R S m1 m2 a0 f0 l0 I M1 H1 MI nowb Cin false
         (@nil byte, @nil byte, @nil byte, @nil byte) (@nil byte, @nil byte, @nil byte).
       entailer!. }
  (* not flood *)
  apply semax_if_seq. forward_if. 2: { hhs3_p3_B_absurd. }
  forward.
  freeze FZ2 := - (hbytes Tsh T0 (offset_val 272 (l_snap L))).
  eapply semax_seq'.
  forward_call (hs_lic (sn_hs (hhs3_p3_snap x25519 R L)), nowb).
  1: { change (hs_lic (sn_hs (hhs3_p3_snap x25519 R L))) with Int64.zero. rewrite Int64.signed_zero. rep_lia. }
  apply ENTAIL_refl.
  unfold MORE_COMMANDS, abbreviate. forward.
  thaw FZ2. subst T0.
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p3_B_snap_open Tsh (l_snap L) (hhs3_p3_snap x25519 R L) FCsn L2 L3 L4 L5 L8))).
  change (hs_ts (sn_hs (hhs3_p3_snap x25519 R L))) with (hs_ts (p_hs (hhs3_PA0 x25519 R L))) in E4.
  change (hs_lic (sn_hs (hhs3_p3_snap x25519 R L))) with (hs_lic (p_hs (hhs3_PA0 x25519 R L))).
  destruct (not_flood (hs_lic (p_hs (hhs3_PA0 x25519 R L))) nowb) eqn:E5.
  2: { forward.
       assert (Eacc: hhs3_p3_acc x25519 aead_dec R L M1 nowb = false)
         by (unfold hhs3_p3_acc; rewrite EB, E1; cbn beta iota zeta; rewrite E2, E3; cbn beta iota zeta;
             rewrite E4, E5; reflexivity).
       sep_apply (@data_at_data_at_ HCS Tsh t_mcinit).
       hhs3_p3_B_close R S m1 m2 a0 f0 l0 I M1 H1 MI nowb Cin false
         (@nil byte, @nil byte, @nil byte, @nil byte) (@nil byte, @nil byte, @nil byte).
       entailer!. }
  (* accepted *)
  forward.
  assert (Eacc: hhs3_p3_acc x25519 aead_dec R L M1 nowb = true)
    by (unfold hhs3_p3_acc; rewrite EB, E1; cbn beta iota zeta; rewrite E2, E3; cbn beta iota zeta;
        rewrite E4, E5; reflexivity).
  hhs3_p3_B_close R S m1 m2 a0 f0 l0 I M1 H1 MI nowb Cin true (s, key, ck, h) (t, ck2, h2).
  unfold hhs3_p3_civ. cbv beta iota.
  entailer!.
Qed.

End P3B.
