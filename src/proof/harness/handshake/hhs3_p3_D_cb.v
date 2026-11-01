(* law handshake, phase P3, segment D, part: POS c_hck, c_ridx, c_lic.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers (adapted from hhs3_p5_D_ca_view / hhs3_p5_D_cc_view)            *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hhs3_p3_D_cb_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

#[local] Instance hhs3_p3_D_cb_CCHW : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

Local Open Scope logic.

Lemma hhs3_p3_D_cb_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hhs3_p3_D_cb_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_handshake (Tstruct HC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_handshake hhs3_p3_D_cb_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hhs3_p3_D_cb_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_handshake (Tstruct HC._wg_peer noattr) [StructField HC._handshake] p = hs_addr p.
Proof. intros H. apply hhs3_p3_D_cb_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hhs3_p3_D_cb_fc_hs p f : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible Noise.CS t_peer [StructField f; StructField prot_repr3.I._handshake] p ->
  @field_compatible Noise.CS t_hs [StructField f] (hs_addr p).
Proof.
  intros H H1. apply (field_compatible_app [StructField f] t_peer [StructField prot_repr3.I._handshake]) in H1.
  rewrite field_address_offset in H1 by auto with field_compatible. exact H1.
Qed.

Lemma hhs3_p3_D_cb_hscs : cs_preserve_type Noise.CS W_handshake (@coeq _ _ hhs3_p3_D_cb_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3_p3_D_cb_ridx sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_index] (Vint v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index; StructField HC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField HC._remote_index; StructField HC._handshake]
    with ([StructField HC._remote_index] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index] [StructField HC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hhs3_p3_D_cb_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p3_D_cb_CCE sh t_hs
           [StructField prot_repr3.I._remote_index] (Vint v) (Vint v) (JMeq_refl _) hhs3_p3_D_cb_hscs)).
Qed.

Lemma hhs3_p3_D_cb_lic sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr)
    [StructField HC._last_initiation_consumption; StructField HC._handshake] (Vlong v) p.
Proof.
  intros H.
  change [StructField HC._last_initiation_consumption; StructField HC._handshake]
    with ([StructField HC._last_initiation_consumption] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._last_initiation_consumption]
             [StructField HC._handshake] (Vlong v) (Vlong v) p (JMeq_refl _)).
  rewrite hhs3_p3_D_cb_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p3_D_cb_CCE sh t_hs
           [StructField prot_repr3.I._last_initiation_consumption] (Vlong v) (Vlong v) (JMeq_refl _)
           hhs3_p3_D_cb_hscs)).
Qed.

Lemma hhs3_p3_D_cb_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

Lemma hhs3_p3_D_cb_hash sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._hash] (bytes l) (hs_addr p) = hbytes sh l (offset_val 264 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p3_D_cb_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply hhs3_p3_D_cb_tuchar_cs.
Qed.

Lemma hhs3_p3_D_cb_ck sh p l : @field_compatible Noise.CS t_peer [] p -> Zlength l = 32 ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._chaining_key] (bytes l) (hs_addr p) = hbytes sh l (offset_val 296 p).
Proof.
  intros H Hl. unfold hbytes. rewrite Hl. rewrite field_at_data_at.
  rewrite field_address_offset by (apply hhs3_p3_D_cb_fc_hs; auto with field_compatible).
  unfold hs_addr. rewrite offset_offset_val.
  apply hhs3_p3_D_cb_tuchar_cs.
Qed.

(* the peer without the handshake's hash, chaining_key, remote_index, last consumption *)
Definition hhs3_p3_D_cb_other (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint (hs_state H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._static_identity] (hs_sid H) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._ephemeral_private] (bytes (hs_eph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._remote_ephemeral] (bytes (hs_reph H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._preshared_key] (bytes (hs_psk H)) h *
   @field_at Noise.CS sh t_hs [StructField prot_repr3.I._latest_timestamp] (bytes (hs_ts H)) h *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Definition hhs3_p3_D_cb_view (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in
  (@field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index; StructField HC._handshake]
     (Vint (hs_rindex H)) p *
   @field_at W_handshake sh (Tstruct HC._wg_peer noattr)
     [StructField HC._last_initiation_consumption; StructField HC._handshake] (Vlong (hs_lic H)) p *
   hbytes sh (hs_hash H) (offset_val 264 p) * hbytes sh (hs_ck H) (offset_val 296 p) *
   hhs3_p3_D_cb_other sh p P).

Lemma hhs3_p3_D_cb_view_eq sh p P :
  peer_rep sh p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) && hhs3_p3_D_cb_view sh p P.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (_ & _ & _ & _ & _ & Lh & Lck & _).
    apply andp_right; [apply prop_right; split; auto |].
    unfold hhs3_p3_D_cb_view, hhs3_p3_D_cb_other. cbv zeta.
    rewrite <- (hhs3_p3_D_cb_ridx sh p _ Hfc), <- (hhs3_p3_D_cb_lic sh p _ Hfc),
      <- (hhs3_p3_D_cb_hash sh p _ Hfc Lh), <- (hhs3_p3_D_cb_ck sh p _ Hfc Lck).
    Intros lk. Exists lk. cancel.
  - Intros. rename H into Hfc, H0 into Hok.
    pose proof Hok as (_ & _ & _ & _ & _ & Lh & Lck & _).
    unfold hhs3_p3_D_cb_view, hhs3_p3_D_cb_other. cbv zeta.
    rewrite <- (hhs3_p3_D_cb_ridx sh p _ Hfc), <- (hhs3_p3_D_cb_lic sh p _ Hfc),
      <- (hhs3_p3_D_cb_hash sh p _ Hfc Lh), <- (hhs3_p3_D_cb_ck sh p _ Hfc Lck).
    unfold peer_rep. Intros lk.
    apply andp_right; [apply prop_right; auto |].
    unfold hs_rep. rewrite (prop_true_andp (hs_ok (p_hs P))) by exact Hok.
    Exists lk. cancel.
Qed.

Lemma hhs3_p3_D_cb_view_fold sh p P h ck ri lic :
  @field_compatible Noise.CS t_peer [] p -> hs_ok (p_hs P) ->
  hs_hash (p_hs P) = h -> hs_ck (p_hs P) = ck -> hs_rindex (p_hs P) = ri -> hs_lic (p_hs P) = lic ->
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index; StructField HC._handshake]
    (Vint ri) p *
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr)
    [StructField HC._last_initiation_consumption; StructField HC._handshake] (Vlong lic) p *
  hbytes sh h (offset_val 264 p) * hbytes sh ck (offset_val 296 p) * hhs3_p3_D_cb_other sh p P
  |-- peer_rep sh p P.
Proof.
  intros Hfc Hok Eh Eck Eri Elic. subst h ck ri lic.
  rewrite hhs3_p3_D_cb_view_eq. apply andp_right; [apply prop_right; auto |].
  unfold hhs3_p3_D_cb_view. cancel.
Qed.

(* the snapshot: its last consumption at the world, the rest *)
Definition hhs3_p3_D_cb_srest (sh: share) (s: val) (sn: hsnap) : mpred :=
  let E := sn_entry sn in let H := sn_hs sn in
  (@field_at HCS sh t_hsnap (DOT HC._peer) (e_peer E) s *
   @field_at HCS sh t_hsnap (DOT HC._next) (sn_next sn) s *
   @field_at HCS sh t_hsnap (DOT HC._hashed) (Val.of_bool (sn_hashed sn)) s * spacer sh 17 20 s *
   @field_at HCS sh t_hsnap (DOT HC._type) (Vint (e_type E)) s *
   @field_at HCS sh t_hsnap (DOT HC._index) (Vint (e_index E)) s *
   @field_at HCS sh t_hsnap (DOT HC._state) (Vint (hs_state H)) s *
   @field_at HCS sh t_hsnap (DOT HC._static_identity) (hs_sid H) s *
   @field_at HCS sh t_hsnap (DOT HC._ephemeral_private) (bytes (hs_eph H)) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_static) (bytes (hs_rstatic H)) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_ephemeral) (bytes (hs_reph H)) s *
   @field_at HCS sh t_hsnap (DOT HC._precomputed_static_static) (bytes (hs_ss H)) s *
   @field_at HCS sh t_hsnap (DOT HC._preshared_key) (bytes (hs_psk H)) s *
   @field_at HCS sh t_hsnap (DOT HC._hash) (bytes (hs_hash H)) s *
   @field_at HCS sh t_hsnap (DOT HC._chaining_key) (bytes (hs_ck H)) s *
   @field_at HCS sh t_hsnap (DOT HC._latest_timestamp) (bytes (hs_ts H)) s *
   @field_at HCS sh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex H)) s).

Lemma hhs3_p3_D_cb_sncs : cs_preserve_type HCS W_handshake (@coeq _ _ hhs3_p3_D_cb_CCHW) t_hsnap = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3_p3_D_cb_snap sh s sn :
  @data_at HCS sh t_hsnap (hsnap_val sn) s =
  @field_at W_handshake sh t_hsnap (DOT HC._last_initiation_consumption) (Vlong (hs_lic (sn_hs sn))) s *
  hhs3_p3_D_cb_srest sh s sn.
Proof.
  (* unfold_data_at takes ~100 s here; the same steps by hand (as in hhs3_p3_B_snap_open) are fast *)
  pose proof (@field_at_Tstruct HCS sh t_hsnap [] HH._hs_snap noattr (hsnap_val sn) (hsnap_val sn) s eq_refl
                (JMeq_refl _)) as HT.
  simpl co_members in HT. lazy beta iota zeta delta [nested_sfieldlist_at] in HT.
  simpl in HT. unfold withspacer in HT. simpl in HT. unfold hsnap_val in HT. simpl in HT.
  unfold hsnap_val, hhs3_p3_D_cb_srest.
  unfold data_at at 1. rewrite HT. clear HT.
  rewrite <- (@field_at_change_composite HCS W_handshake hhs3_p3_D_cb_CCHW sh t_hsnap (DOT HC._last_initiation_consumption)
               (Vlong (hs_lic (sn_hs sn))) (Vlong (hs_lic (sn_hs sn))) (JMeq_refl _) hhs3_p3_D_cb_sncs).
  apply pred_ext; cancel.
Qed.

(* the harness's ci: its state's ck and h as byte buffers, the rest *)
Lemma hhs3_p3_D_cb_ci sh ci ck h kv sv tv :
  @field_compatible HCS t_mcinit [] ci -> Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mcinit (mcinit_val ck h kv sv tv) ci =
  hbytes sh ck ci * hbytes sh h (offset_val 32 ci) *
  @field_at HCS sh t_mcinit (DOT HC._key) kv ci * @field_at HCS sh t_mcinit (DOT HC._spub) sv ci *
  @field_at HCS sh t_mcinit (DOT HC._ts) tv ci.
Proof.
  intros Hfc Lck Lh. unfold mcinit_val, hbytes. rewrite Lck, Lh.
  unfold_data_at (@data_at HCS _ _ _ ci).
  unfold_field_at 1%nat.
  rewrite (@field_at_data_at HCS sh t_mcinit (DOT HC._st DOT HC._ck)),
    (@field_at_data_at HCS sh t_mcinit (DOT HC._st DOT HC._h)).
  rewrite !(@field_address_offset HCS) by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by exact (field_compatible_isptr _ _ _ Hfc).
  apply pred_ext; cancel.
Qed.

(* the initiation message: its sender index at the world, the rest *)
Section NoiseFields.
#[local] Existing Instance Noise.CS.

Definition hhs3_p3_D_cb_irest (sh: share) (m: val) (M: init_msg) : mpred :=
  field_at sh t_init (DOT I._header) (Vint (im_type M)) m *
  field_at sh t_init (DOT I._unencrypted_ephemeral) (bytes (im_eph M)) m *
  field_at sh t_init (DOT I._encrypted_static) (bytes (im_encs M)) m *
  field_at sh t_init (DOT I._encrypted_timestamp) (bytes (im_enct M)) m *
  field_at sh t_init (DOT I._macs) (bytes (im_mac1 M), bytes (im_mac2 M)) m.

Lemma hhs3_p3_D_cb_init sh m M :
  im_ok M ->
  init_rep sh m M =
  @field_at W_handshake sh (Tstruct HC._message_handshake_initiation noattr) (DOT HC._sender_index) (Vint (im_sender M)) m *
  hhs3_p3_D_cb_irest sh m M.
Proof.
  intros Hok. unfold init_rep, hhs3_p3_D_cb_irest, init_val. rewrite prop_true_andp by exact Hok.
  unfold_data_at (data_at _ t_init _ m).
  rewrite (f_equal (fun f => f m) (@field_at_change_composite Noise.CS W_handshake hhs3_p3_D_cb_CCE sh t_init
           (DOT I._sender_index) (Vint (im_sender M)) (Vint (im_sender M)) (JMeq_refl _) ltac:(vm_compute; reflexivity))).
  apply pred_ext; cancel.
Qed.
End NoiseFields.

Lemma hhs3_p3_D_cb_init_fold sh m M si : im_ok M -> im_sender M = si ->
  @field_at W_handshake sh (Tstruct HC._message_handshake_initiation noattr) (DOT HC._sender_index) (Vint si) m *
  hhs3_p3_D_cb_irest sh m M |-- init_rep sh m M.
Proof. intros Hok <-. rewrite (hhs3_p3_D_cb_init sh m M Hok). apply derives_refl. Qed.

(* pa's handshake after consume_initiation (one reference dropped again) *)
Lemma hhs3_p3_D_cb_new x25519 R L M1 nowb t ck h :
  let H := p_hs (hhs3_PA2 (hhs3_p3_new x25519 R L M1 nowb (t, ck, h))) in
  hs_hash H = h /\ hs_ck H = ck /\ hs_rindex H = im_sender M1 /\
  hs_lic H = last_consumption (hs_lic (sn_hs (hhs3_p3_snap x25519 R L))) nowb.
Proof. repeat split; reflexivity. Qed.

Lemma hhs3_p3_D_cb_M1m x25519 R M1 : im_sender (hhs3_M1m x25519 R M1) = im_sender M1.
Proof. reflexivity. Qed.

Section Part.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_D_cb_ok {Espec: OracleKind} gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2 (Rp: ret_assert) :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hhs3_p3_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2)
    (Ssequence hhs3_p3_D_chck (Ssequence hhs3_p3_D_cridx hhs3_p3_D_clic))
    (overridePost (hhs3_p3_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2) Rp).
Proof.
  intros HH. destruct Rp as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hhs3_p3_D_Q, hhs3_p3_D_st, hhs3_Delta, hhs3_p3_D_chck, hhs3_p3_D_cridx, hhs3_p3_D_clic.
  simplify_func_tycontext.
  destruct CI2 as [[t ck] h]. destruct CI1 as [[[s key] ck1] h1].
  destruct (hhs3_p3_D_cb_new x25519 R L M1 nowb t ck h) as (Eh & Eck & Eri & Elic).
  set (P := hhs3_PA2 (hhs3_p3_new x25519 R L M1 nowb (t, ck, h))) in *.
  set (sn := hhs3_p3_snap x25519 R L) in *.
  unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  abbreviate_semax.
  Intros.
  rewrite (hhs3_p3_D_cb_view_eq Tsh (l_pa L) P). Intros.
  assert_PROP (im_ok (hhs3_M1m x25519 R M1)) as IMok.
  { unfold init_rep. entailer!. }
  match goal with Hx: @field_compatible Noise.CS t_peer [] (l_pa L) |- _ => rename Hx into Hfc end.
  match goal with Hx: hs_ok (p_hs P) |- _ => pose proof Hx as (_ & _ & _ & _ & _ & Lh & Lck & _) end.
  rewrite Eh in Lh. rewrite Eck in Lck.
  assert_PROP (@field_compatible HCS t_mcinit [] (l_ci L)) as FCci.
  { entailer!. }
  rewrite (hhs3_p3_D_cb_init Ews m1 _ IMok).
  rewrite (hhs3_p3_D_cb_snap Tsh (l_snap L) (hhs3_p3_snap x25519 R L)).
  unfold hhs3_p3_D_cb_view. rewrite Eh, Eck, Eri, Elic, hhs3_p3_D_cb_M1m.
  unfold hhs3_p3_civ.
  rewrite (hhs3_p3_D_cb_ci Tsh (l_ci L) ck h _ _ _ FCci Lck Lh).
  Intros.
  freeze FZ := - (hbytes Tsh h (offset_val 264 (l_pa L))) (hbytes Tsh ck (offset_val 296 (l_pa L)))
    (hbytes Tsh ck (l_ci L)) (hbytes Tsh h (offset_val 32 (l_ci L)))
    (field_at Tsh (Tstruct HC._wg_peer noattr) [StructField HC._remote_index; StructField HC._handshake] _ (l_pa L))
    (field_at Tsh (Tstruct HC._wg_peer noattr) [StructField HC._last_initiation_consumption; StructField HC._handshake] _ (l_pa L))
    (field_at Ews (Tstruct HC._message_handshake_initiation noattr) (DOT HC._sender_index) _ m1)
    (field_at Tsh t_hsnap (DOT HC._last_initiation_consumption) _ (l_snap L)).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + forward_call (Tsh, offset_val 264 (l_pa L), h, Tsh, offset_val 32 (l_ci L), h).
    { entailer!. rewrite Lh. pose proof (field_compatible_isptr _ _ _ FCci) as Ici.
      pose proof (field_compatible_isptr _ _ _ Hfc) as Ipa.
      destruct (l_pa L); try contradiction. destruct (l_ci L); try contradiction.
      simpl. rewrite ?Ptrofs.add_assoc. reflexivity. }
    rewrite hhs3_p3_D_cb_eqb_refl.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'82 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward_call (Tsh, offset_val 296 (l_pa L), ck, Tsh, l_ci L, ck).
      { entailer!. rewrite Lck. pose proof (field_compatible_isptr _ _ _ FCci) as Ici.
        pose proof (field_compatible_isptr _ _ _ Hfc) as Ipa.
        destruct (l_pa L); try contradiction. destruct (l_ci L); try contradiction.
        simpl. rewrite ?Ptrofs.add_assoc, ?Ptrofs.add_zero. reflexivity. }
      rewrite hhs3_p3_D_cb_eqb_refl. forward. entailer!. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward_if.
    { forward_call tt. all: [> exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
    forward. entailer!.
  + forward. apply ENTAIL_refl.
  + match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    * apply ENTAIL_refl.
    * forward. forward. forward_if.
      { forward_call tt. all: [> exfalso; match goal with Hc: _ = Int.zero |- _ => rewrite Int.eq_true in Hc; exact (Int.one_not_zero Hc) end | entailer!]. }
      forward. entailer!.
    * forward. apply ENTAIL_refl.
    * match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      -- apply ENTAIL_refl.
      -- forward. forward_call (hs_lic (sn_hs (hhs3_p3_snap x25519 R L)), nowb).
         forward. forward_if.
         { forward_call tt. all: [> exfalso; match goal with Hc: _ = Int.zero |- _ => rewrite Int64.eq_true in Hc; exact (Int.one_not_zero Hc) end | entailer!]. }
         forward. entailer!.
      -- forward. apply ENTAIL_refl.
      -- thaw FZ.
         match goal with Hx: hs_ok (p_hs P) |- _ => rename Hx into Hok end.
         sep_apply (hhs3_p3_D_cb_view_fold Tsh (l_pa L) P h ck (im_sender M1)
                      (last_consumption (hs_lic (sn_hs sn)) nowb) Hfc Hok Eh Eck Eri Elic).
         sep_apply (hhs3_p3_D_cb_init_fold Ews m1 (hhs3_M1m x25519 R M1) (im_sender M1) IMok
                      (hhs3_p3_D_cb_M1m x25519 R M1)).
         sep_apply (derives_refl' _ _ (eq_sym (hhs3_p3_D_cb_ci Tsh (l_ci L) ck h (bytes (kdf2 ck1 (hhs3_ssb x25519 R)))
                      (bytes s) (bytes t) FCci Lck Lh))).
         sep_apply (derives_refl' _ _ (eq_sym (hhs3_p3_D_cb_snap Tsh (l_snap L) (hhs3_p3_snap x25519 R L)))).
         unfold POSTCONDITION, abbreviate.
         (* not simpl RA_normal: it does not terminate on this SEP *)
         match goal with |- ?A |-- RA_normal (Build_ret_assert ?X _ _ _) => change (A |-- X) end.
         unfold hhs3_p3_civ.
         entailer!.
Qed.

End Part.
