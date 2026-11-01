(* law replay: the loop body, segment L3 (kind 2: CHECK(!acc); !acc: CHECK(ret == NULL && hs_same(&snap,
   &pa.handshake) && pa.refcount == 1); acc: CHECK(ret == &pa && refcount 2), wg_peer_put(ret), CHECKs of
   refcount, state, latest_timestamp, last_initiation_consumption, hash and chaining key; latest = ci.ts,
   last = m_last_consumption(last, now), copy_init(accepted, m), have_accepted = 1).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

#[local] Instance hrp3_segL3_CCE : change_composite_env Noise.CS W_replay.
Proof. make_cs_preserve Noise.CS W_replay. Defined.

Lemma hrp3_segL3_pa x25519 F V PA lat last :
  hrp3_pa_ok (hrp3_PA0 x25519 F V) PA lat last ->
  p_refs PA = Int.one /\ hs_sid (p_hs PA) = id_addr (f_wb F) /\ hs_lic (p_hs PA) = last /\
  p_device PA = f_wb F.
Proof. intros (st & reph & h & ck & ri & ->). repeat split; reflexivity. Qed.

Lemma hrp3_segL3_cmp x25519 F V PA lat last :
  hrp3_pa_ok (hrp3_PA0 x25519 F V) PA lat last ->
  hs_cmp_pre (snap_of (hrp3_TB0 (f_pa F)) (hs_addr (f_pa F)) (hrp3_E0 (f_pa F)) (p_hs PA))
    (hrp3_TB0 (f_pa F)) (f_pa F) (f_wb F) PA (hrp3_E0 (f_pa F)).
Proof.
  intros Hpa. destruct (hrp3_segL3_pa _ _ _ _ _ _ Hpa) as (_ & Hsid & _).
  unfold hs_cmp_pre, snap_of. cbn [sn_entry sn_hs sn_next]. split; [| split; [| split; [| split; [| split]]]].
  - unfold t_entry, hrp3_TB0, t_add. cbn [t_D sfind]. rewrite if_true by reflexivity. reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hsid.
  - exact Hsid.
  - left. reflexivity.
Qed.

(* the reference count of a peer, at main's compspecs *)
Lemma hrp3_segL3_refs sh p r :
  peer_refs_rep sh p r = @field_at W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._refcount] (Vint r) p.
Proof.
  unfold peer_refs_rep.
  assert (Hc: cs_preserve_type Noise.CS W_replay (@coeq _ _ hrp3_segL3_CCE) t_peer = true) by (vm_compute; reflexivity).
  assert (E := @field_at_change_composite Noise.CS W_replay hrp3_segL3_CCE sh t_peer [StructField I._refcount]
                 (Vint r) (Vint r) (JMeq_refl _) Hc).
  exact (f_equal (fun f => f p) E).
Qed.

(* peer_rep without its device field and its reference count *)
Definition hrp3_segL3_rest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hrp3_segL3_split sh p P :
  peer_rep sh p P =
  (!! @field_compatible Noise.CS t_peer [] p &&
   (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p * peer_refs_rep sh p (p_refs P) *
    hrp3_segL3_rest sh p P))%logic.
Proof.
  unfold peer_rep, hrp3_segL3_rest, peer_refs_rep. apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Lemma hrp3_segL3_open sh p P :
  peer_rep sh p P |--
  (!! @field_compatible Noise.CS t_peer [] p &&
   (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
    @field_at W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._refcount] (Vint (p_refs P)) p *
    hrp3_segL3_rest sh p P))%logic.
Proof. rewrite hrp3_segL3_split, hrp3_segL3_refs. apply derives_refl. Qed.

Lemma hrp3_segL3_fold sh p P :
  @field_compatible Noise.CS t_peer [] p ->
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._refcount] (Vint (p_refs P)) p *
   hrp3_segL3_rest sh p P)%logic |-- peer_rep sh p P.
Proof.
  intros Hfc. rewrite hrp3_segL3_split, hrp3_segL3_refs. apply andp_right; [apply prop_right; exact Hfc | apply derives_refl].
Qed.

Lemma hrp3_segL3_mbuf M M' p : hrp3_mbuf true M p |-- hrp3_mbuf false M' p.
Proof.
  unfold hrp3_mbuf. cbv iota. apply sepcon_derives; [apply derives_refl |].
  unfold init_rep. apply andp_left2. apply data_at_data_at_.
Qed.

#[local] Instance hrp3_segL3_CCEH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

Lemma hrp3_segL3_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_replay (Tstruct RC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_replay hrp3_segL3_CCE t_peer); [vm_compute; reflexivity | exact H].
Qed.

Lemma hrp3_segL3_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_replay (Tstruct RC._wg_peer noattr) [StructField RC._handshake] p = hs_addr p.
Proof. intros H. apply hrp3_segL3_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hrp3_segL3_fc_hs p f : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible Noise.CS t_peer [StructField f; StructField prot_repr3.I._handshake] p ->
  @field_compatible Noise.CS t_hs [StructField f] (hs_addr p).
Proof.
  intros H H1. apply (field_compatible_app [StructField f] t_peer [StructField prot_repr3.I._handshake]) in H1.
  rewrite field_address_offset in H1 by auto with field_compatible. exact H1.
Qed.

Lemma hrp3_segL3_hscs : cs_preserve_type Noise.CS W_replay (@coeq _ _ hrp3_segL3_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hrp3_segL3_state sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint v) (hs_addr p) =
  @field_at W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._state; StructField RC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField RC._state; StructField RC._handshake] with ([StructField RC._state] ++ [StructField RC._handshake]).
  rewrite (@field_at_app W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._state] [StructField RC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hrp3_segL3_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_replay hrp3_segL3_CCE sh t_hs
           [StructField prot_repr3.I._state] (Vint v) (Vint v) (JMeq_refl _) hrp3_segL3_hscs)).
Qed.

Lemma hrp3_segL3_lic sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong v) (hs_addr p) =
  @field_at W_replay sh (Tstruct RC._wg_peer noattr)
    [StructField RC._last_initiation_consumption; StructField RC._handshake] (Vlong v) p.
Proof.
  intros H.
  change [StructField RC._last_initiation_consumption; StructField RC._handshake]
    with ([StructField RC._last_initiation_consumption] ++ [StructField RC._handshake]).
  rewrite (@field_at_app W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._last_initiation_consumption]
             [StructField RC._handshake] (Vlong v) (Vlong v) p (JMeq_refl _)).
  rewrite hrp3_segL3_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_replay hrp3_segL3_CCE sh t_hs
           [StructField prot_repr3.I._last_initiation_consumption] (Vlong v) (Vlong v) (JMeq_refl _) hrp3_segL3_hscs)).
Qed.

Lemma hrp3_segL3_hash sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._hash] (bytes l) (hs_addr p) = hbytes sh l (offset_val 264 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hrp3_segL3_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hrp3_segL3_ck sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._chaining_key] (bytes l) (hs_addr p) = hbytes sh l (offset_val 296 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hrp3_segL3_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hrp3_segL3_ts sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 12 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._latest_timestamp] (bytes l) (hs_addr p) = hbytes sh l (offset_val 328 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hrp3_segL3_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hrp3_segL3_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

(* the peer without device, refcount, and the handshake's state, last consumption, hash, chaining key, timestamp *)
Definition hrp3_segL3_other (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._static_identity] (hs_sid H) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._ephemeral_private] (bytes (hs_eph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_ephemeral] (bytes (hs_reph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._preshared_key] (bytes (hs_psk H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Definition hrp3_segL3_view (sh: share) (p: val) (P: peer) (r: int) : mpred :=
  let H := p_hs P in
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._refcount] (Vint r) p *
   @field_at W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._state; StructField RC._handshake]
     (Vint (hs_state H)) p *
   @field_at W_replay sh (Tstruct RC._wg_peer noattr)
     [StructField RC._last_initiation_consumption; StructField RC._handshake] (Vlong (hs_lic H)) p *
   hbytes sh (hs_hash H) (offset_val 264 p) * hbytes sh (hs_ck H) (offset_val 296 p) *
   hbytes sh (hs_ts H) (offset_val 328 p) * hrp3_segL3_other sh p P)%logic.

Lemma hrp3_segL3_aopen sh p P :
  peer_rep sh p P |--
  (!! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) && hrp3_segL3_view sh p P (p_refs P))%logic.
Proof.
  unfold peer_rep, hs_rep. Intros. rename H into Hfc, H0 into Hok.
  pose proof Hok as (_ & _ & _ & _ & _ & Lh & Lck & Lts).
  apply andp_right; [apply prop_right; split; auto |].
  unfold hrp3_segL3_view, hrp3_segL3_other. cbv zeta.
  rewrite <- (hrp3_segL3_state sh p _ Hfc), <- (hrp3_segL3_lic sh p _ Hfc), <- (hrp3_segL3_hash sh p _ Hfc Lh),
    <- (hrp3_segL3_ck sh p _ Hfc Lck), <- (hrp3_segL3_ts sh p _ Hfc Lts), <- hrp3_segL3_refs.
  unfold peer_refs_rep. cancel.
Qed.

Lemma hrp3_segL3_afold sh p P r :
  @field_compatible Noise.CS t_peer [] p -> hs_ok (p_hs P) ->
  hrp3_segL3_view sh p P r |-- peer_rep sh p (p_set_refs P r).
Proof.
  intros Hfc Hok. pose proof Hok as (_ & _ & _ & _ & _ & Lh & Lck & Lts).
  unfold hrp3_segL3_view, hrp3_segL3_other. cbv zeta.
  rewrite <- (hrp3_segL3_state sh p _ Hfc), <- (hrp3_segL3_lic sh p _ Hfc), <- (hrp3_segL3_hash sh p _ Hfc Lh),
    <- (hrp3_segL3_ck sh p _ Hfc Lck), <- (hrp3_segL3_ts sh p _ Hfc Lts), <- hrp3_segL3_refs.
  unfold peer_rep, hs_rep, peer_refs_rep. cbn [p_set_refs p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  Intros lk. Exists lk.
  apply andp_right; [apply prop_right; split; assumption | cancel].
Qed.

Lemma hrp3_segL3_tceq sh d p R : sepalg.nonidentity sh ->
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p * R)%logic |-- denote_tc_test_eq p p.
Proof.
  intros Hsh. apply denote_tc_test_eq_split; apply sepcon_valid_pointer1; apply field_at_valid_ptr0; auto;
    vm_compute; reflexivity.
Qed.

Lemma hrp3_segL3_putpre sh p d r : p <> nullval ->
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p *
   @field_at W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._refcount] (Vint r) p)%logic |--
  (if eq_dec p nullval then emp
   else (peer_refs_rep sh p r * @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p))%logic.
Proof. intros Hp. rewrite if_false by exact Hp. rewrite hrp3_segL3_refs. cancel. Qed.

Lemma hrp3_segL3_putpost sh p d r : p <> nullval ->
  (if eq_dec p nullval then emp
   else (peer_refs_rep sh p r * @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p))%logic |--
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p *
   @field_at W_replay sh (Tstruct RC._wg_peer noattr) [StructField RC._refcount] (Vint r) p)%logic.
Proof. intros Hp. rewrite if_false by exact Hp. rewrite hrp3_segL3_refs. cancel. Qed.

Lemma hrp3_segL3_hout sh l p : hbytes sh l p |-- hout sh (Zlength l) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hrp3_segL3_mbuf_any b M p :
  hrp3_mbuf b M p |-- (@malloc_token W_replay Ews t_init p * @data_at_ Noise.CS Ews t_init p)%logic.
Proof.
  unfold hrp3_mbuf. apply sepcon_derives; [apply derives_refl |].
  destruct b; [| apply derives_refl]. unfold init_rep. apply andp_left2. apply data_at_data_at_.
Qed.

Lemma hrp3_segL3_ci sh ci ck h kv sv t :
  @field_compatible HCS t_mcinit [] ci -> Zlength ck = 32 -> Zlength h = 32 -> Zlength kv = 32 ->
  Zlength sv = 32 -> Zlength t = 12 ->
  @data_at HCS sh t_mcinit (mcinit_val ck h kv sv (bytes t)) ci =
  (hbytes sh ck ci * hbytes sh h (offset_val 32 ci) * @data_at HCS sh (tarray tuchar 32) kv (offset_val 64 ci) *
   @data_at HCS sh (tarray tuchar 32) sv (offset_val 96 ci) * hbytes sh t (offset_val 128 ci))%logic.
Proof.
  intros Hfc Lck Lh Lkv Lsv Lt. unfold mcinit_val, hbytes. rewrite Lck, Lh, Lt.
  unfold_data_at (@data_at HCS _ _ _ ci).
  unfold_field_at 1%nat.
  rewrite !(@field_at_data_at HCS).
  rewrite !(@field_address_offset HCS) by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by exact (field_compatible_isptr _ _ _ Hfc).
  apply pred_ext; cancel.
Qed.

Lemma hrp3_segL3_hout2 sh (l l': list byte) p : Zlength l = Zlength l' -> hbytes sh l p |-- hout sh (Zlength l') p.
Proof. intros E. rewrite <- E. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hrp3_segL3_init_ sh p M : init_rep sh p M |-- @data_at_ Noise.CS sh t_init p.
Proof. unfold init_rep. apply andp_left2. apply data_at_data_at_. Qed.

Ltac hrp3_segL3_false :=
  match goal with Hc: Int.repr (Z.b2z _) = Int.zero |- _ =>
    rewrite ?Int64.eq_true, ?Int.eq_true in Hc; exact (Int.one_not_zero Hc) end.

Lemma hrp3_segL3_ok {Espec: OracleKind} x25519 aead_enc aead_dec (F: hrp3_fix) (FR: mpred) V sp ap mp steps i R :
  hrp3_facts -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  semax (hrp3_Delta x25519 aead_enc aead_dec)
    (hrp3_PL2b x25519 aead_dec F V sp ap mp steps FR i) hrp3_segL3
    (loop1_ret_assert (hrp3_Icont x25519 aead_dec F V sp ap mp steps FR i) R).
Proof.
  intros HF HX HA.
  destruct R as [Rn Rb Rc Rr]. unfold loop1_ret_assert.
  destruct F as [gv wa wb ita itb pta ptb pa pb ia ib rawa rawb psk ssb latest ci snap].
  unfold hrp3_PL2b, hrp3_Delta, hrp3_lvars, hrp3_temps, hrp3_segL3. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  Intros Y M kind.
  destruct Y as [S TA PB PA lat last now hs Ms ha Ma].
  cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma] in *.
  unfold hrp3_world, hrp3_globs, app. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  set (F0 := {| f_gv := gv; f_wa := wa; f_wb := wb; f_ita := ita; f_itb := itb; f_pta := pta; f_ptb := ptb;
    f_pa := pa; f_pb := pb; f_ia := ia; f_ib := ib; f_rawa := rawa; f_rawb := rawb; f_psk := psk; f_ssb := ssb;
    f_latest := latest; f_ci := ci; f_snap := snap |}) in *.
  abbreviate_semax.
  destruct HF as (HM & HR & HC).
  destruct (HM x25519 aead_enc aead_dec) as (HM1 & HM2 & HM3 & HM4 & HM5 & HM6 & HM7 & HM8 & HM9).
  assert (HK2: kind = 2 -> hrp3_accv x25519 aead_dec V lat last now M = None).
  { intros Hk. destruct (H4 Hk) as [-> ->]. destruct H1 as (_&_&_&_&_&_&_&Hacc). cbn [y_ha y_Ma y_latest] in Hacc.
    destruct (Hacc eq_refl) as (t&ck&h&Ht&Hn). unfold hrp3_accv. eapply HM3; eauto. }
  destruct (hrp3_accv x25519 aead_dec V lat last now M) as [[[t ck] h]|] eqn:EA.
  - assert (Hk: kind <> 2) by (intros Hk; specialize (HK2 Hk); discriminate).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    { contradiction. }
    { forward. apply ENTAIL_refl. }
    pose proof H1 as Hinv. destruct H1 as (_ & _ & _ & Hpa & Hlat & Hlast & Hnow & _).
    cbn [y_PA y_latest y_last y_now f_pa f_wb] in Hpa, Hlat, Hlast, Hnow.
    destruct (hrp3_segL3_pa _ _ _ _ _ _ Hpa) as (Hrefs & Hsid & Hlic & Hdev).
    pose proof EA as EA'. unfold hrp3_accv in EA'. destruct (HM4 _ _ _ _ _ _ _ _ _ _ EA') as [Hts Hnn].
    unfold hrp3_ci_rep. Intros kv sv.
    set (P1 := hrp3_pa_after PA M t ck h now).
    assert (HP1: p_refs P1 = Int.repr 2 /\ hs_state (p_hs P1) = Int.repr 2 /\
                 hs_lic (p_hs P1) = last_consumption last now /\ hs_hash (p_hs P1) = h /\
                 hs_ck (p_hs P1) = ck /\ hs_ts (p_hs P1) = t).
    { unfold P1, hrp3_pa_after. cbn. rewrite Hrefs, Hlic. repeat split; reflexivity. }
    destruct HP1 as (Er & Es & El & Eh & Eck & Et).
    clear H5 Hlic Hdev Hsid.
    sep_apply (hrp3_segL3_aopen Tsh pa P1). Intros.
    assert (Hfc: @field_compatible Noise.CS t_peer [] pa) by
      (match goal with Hx: _ |- _ => first [exact Hx | exact (proj1 Hx)] end).
    assert (Hok: hs_ok (p_hs P1)) by (match goal with Hx: _ |- _ => first [exact Hx | exact (proj2 Hx)] end).
    pose proof Hok as (_ & _ & _ & _ & _ & Lh & Lck & _). rewrite Eh in Lh. rewrite Eck in Lck.
    assert (Hpn: pa <> nullval) by (intros ->; exact (field_compatible_isptr _ _ _ Hfc)).
    forward_if.
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    unfold hrp3_segL3_view. rewrite Er, Es, El, Eh, Eck, Et. Intros.
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    + apply ENTAIL_refl.
    + match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp RC._t'30 (Vint Int.one) :: Q) (SEPx R))) end.
      * apply denote_tc_test_eq_split; repeat apply sepcon_valid_pointer1; apply field_at_valid_ptr0; auto;
          vm_compute; reflexivity.
      * forward. forward. change (bool2val (Int.eq (Int.repr 2) (Int.repr 2))) with (Vint Int.one). entailer!.
      * exfalso. auto.
      * forward_if.
        { forward_call tt. all: first [hrp3_segL3_false | entailer!]. }
        forward. entailer!.
    + forward. apply ENTAIL_refl.
    + sep_apply (hrp3_segL3_putpre Tsh pa (p_device P1) (Int.repr 2) Hpn).
      forward_call (gv, S, Tsh, pa, Int.repr 2, p_device P1).
      sep_apply (hrp3_segL3_putpost Tsh pa (p_device P1) (rc_sub1 (Int.repr 2)) Hpn).
      rewrite if_false by exact Hpn.
      change (if Int.eq (rc_sub1 (Int.repr 2)) Int.zero then shim_release S else S) with S.
      change (rc_sub1 (Int.repr 2)) with Int.one. Intros.
      match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      * apply ENTAIL_refl.
      * forward. forward_if.
        { forward_call tt. all: first [hrp3_segL3_false | entailer!]. }
        forward. entailer!.
      * forward. apply ENTAIL_refl.
      * match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
        -- apply ENTAIL_refl.
        -- forward. forward_if.
           { forward_call tt. all: first [hrp3_segL3_false | entailer!]. }
           forward. entailer!.
        -- forward. apply ENTAIL_refl.
        -- assert_PROP (@field_compatible HCS t_mcinit [] ci) as Hfci by entailer!.
           rewrite (hrp3_segL3_ci Tsh ci ck h kv sv t Hfci Lck Lh H1 H6 H7). Intros.
           match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
           ++ apply ENTAIL_refl.
           ++ forward_call (Tsh, offset_val 328 pa, t, Tsh, offset_val 128 ci, t).
              { apply prop_right. simpl. rewrite H7, offset_offset_val. reflexivity. }
              rewrite hrp3_segL3_eqb_refl. forward_if.
              { forward_call tt. all: first [hrp3_segL3_false | entailer!]. }
              forward. entailer!.
           ++ forward. apply ENTAIL_refl.
           ++ match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
              { apply ENTAIL_refl. }
              { forward_call (last, now). forward. forward_if.
                { forward_call tt. all: first [hrp3_segL3_false | entailer!]. }
                forward. entailer!. }
              { forward. apply ENTAIL_refl. }
              match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
              { apply ENTAIL_refl. }
              { forward_call (Tsh, offset_val 264 pa, h, Tsh, offset_val 32 ci, h).
                { apply prop_right. simpl. rewrite Lh, !offset_offset_val. reflexivity. }
                rewrite hrp3_segL3_eqb_refl.
                match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
                  forward_if (PROPx P (LOCALx (temp RC._t'34 (Vint Int.one) :: Q) (SEPx R))) end.
                { forward_call (Tsh, offset_val 296 pa, ck, Tsh, ci, ck).
                  { apply prop_right. simpl. rewrite Lck, !offset_offset_val. simpl Z.add.
                    rewrite ?isptr_offset_val_zero by exact (field_compatible_isptr _ _ _ Hfci). reflexivity. }
                  rewrite hrp3_segL3_eqb_refl. forward. entailer!. }
                { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
                forward_if.
                { forward_call tt. all: first [hrp3_segL3_false | entailer!]. }
                forward. entailer!. }
              { forward. apply ENTAIL_refl. }
              sep_apply (hrp3_segL3_hout2 Tsh lat t latest ltac:(rewrite Hlat, H7; reflexivity)).
              forward_call (Tsh, latest, Tsh, offset_val 128 ci, t).
              { apply prop_right. simpl. rewrite H7. reflexivity. }
              forward_call (last, now).
              sep_apply (hrp3_segL3_mbuf_any ha Ma ap).
              change (hrp3_mbuf true M mp) with (@malloc_token W_replay Ews t_init mp * init_rep Ews mp M)%logic.
              Intros.
              forward_call (Ews, ap, Ews, mp, M).
              forward.
              set (P2 := p_set_refs P1 (Int.sub (Int.add Int.one Int.one) Int.one)).
              set (Y' := mkRDyn S TA PB P2 t (last_consumption last now) now hs Ms true M).
              assert (Hinv': hrp3_inv x25519 aead_dec F0 V Y').
              { destruct Hinv as (Hta & Hd & Hs & _ & _ & _ & _ & _).
                unfold hrp3_inv, Y'; cbn [y_TA y_PB y_PA y_latest y_last y_now y_ha y_Ma].
                split; [exact Hta |]. split; [exact Hd |]. split; [exact Hs |].
                split; [apply (HM2 _ _ lat last); [reflexivity | exact Hpa] |].
                split; [exact H7 |]. split; [apply HM9; auto |]. split; [exact Hnow |].
                intros _. exists t, ck, h. split; [exact Hts | exact Hnn]. }
              assert (AF := hrp3_segL3_afold Tsh pa P1 Int.one Hfc Hok).
              unfold hrp3_segL3_view in AF. rewrite Es, El, Eh, Eck, Et in AF. sep_apply AF.
              assert (CI := hrp3_segL3_ci Tsh ci ck h kv sv t Hfci Lck Lh H1 H6 H7).
              sep_apply (derives_refl' _ _ (eq_sym CI)).
              sep_apply (@data_at_data_at_ HCS Tsh t_mcinit (mcinit_val ck h kv sv (bytes t)) ci).
              sep_apply (hrp3_segL3_init_ Ews mp M).
              sep_apply (data_at_data_at_ Tsh t_hsnap (hsnap_val (snap_of (hrp3_TB0 pa) (hs_addr pa) (hrp3_E0 pa) (p_hs PA))) snap).
              unfold hrp3_Icont, hrp3_St. Exists Y'.
              unfold hrp3_world, hrp3_globs, hrp3_temps, hrp3_lvars, hrp3_mbuf, app.
              unfold Y'. cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma].
              subst F0. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
              entailer!.
              change P2 with (p_set_refs P1 Int.one). apply derives_refl.
  - match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    { match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      - entailer!.
      - forward_if.
        { forward_call tt. { match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
          apply ENTAIL_refl. }
        forward. apply ENTAIL_refl.
      - forward. apply ENTAIL_refl.
      - unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl. }
    { forward. apply ENTAIL_refl. }
    pose proof H1 as Hinv. destruct H1 as (_ & _ & _ & Hpa & Hlat & Hlast & Hnow & _).
    cbn [y_PA y_latest y_last y_now f_pa f_wb] in Hpa, Hlat, Hlast, Hnow.
    destruct (hrp3_segL3_pa _ _ _ _ _ _ Hpa) as (Hrefs & Hsid & Hlic & Hdev).
    pose proof (hrp3_segL3_cmp _ _ _ _ _ _ Hpa) as Hcmp. cbn [f_pa f_wb] in Hcmp.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    { match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      - apply ENTAIL_refl.
      - match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp RC._t'27 (Vint Int.one) :: Q) (SEPx R))) end.
        { forward_call (Tsh, snap, snap_of (hrp3_TB0 pa) (hs_addr pa) (hrp3_E0 pa) (p_hs PA), Tsh, pa, PA, Tsh, itb,
                        hrp3_TB0 pa, hrp3_E0 pa, Tsh, wb, hrp3_DB x25519 F0 V).
          rewrite HM8. forward. entailer!. }
        { exfalso. auto. }
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp RC._t'29 (Vint Int.one) :: Q) (SEPx R))) end.
        { sep_apply (hrp3_segL3_open Tsh pa PA). Intros. forward. forward.
          match goal with Hf: @field_compatible Noise.CS t_peer [] pa |- _ => sep_apply (hrp3_segL3_fold Tsh pa PA Hf) end.
          rewrite Hrefs. change (bool2val (Int.eq Int.one (Int.repr 1))) with (Vint Int.one). entailer!. }
        { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
        forward_if.
        { forward_call tt. { match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
          entailer!. }
        forward. entailer!.
      - forward. apply ENTAIL_refl.
      - unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl. }
    { exfalso. auto. }
    unfold hrp3_Icont, hrp3_St. Exists (mkRDyn S TA PB PA lat last now hs Ms ha Ma).
    unfold hrp3_world, hrp3_globs, hrp3_temps, hrp3_lvars, app.
    cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma].
    subst F0. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
    sep_apply (hrp3_segL3_mbuf M Ma mp).
    sep_apply (data_at_data_at_ Tsh t_hsnap (hsnap_val (snap_of (hrp3_TB0 pa) (hs_addr pa) (hrp3_E0 pa) (p_hs PA))) snap).
    unfold hrp3_ci_rep.
    entailer!.
Qed.
