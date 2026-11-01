(* law handshake: main's phase P1, segment F = statements 28..32: m_label_key x2 and the cookie-key CHECKs, the state CHECK.
   (section P1). *)
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
Require Import WgNoise.proof.harness.handshake.hhs3_p1_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

Lemma hhs3_p1_F_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

#[local] Instance hhs3_p1_F_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

(* a Tsh byte buffer as an Ers part (to share one share with a constant) and the rest *)
Lemma hhs3_p1_F_ers_split bs p : hbytes Tsh bs p = hbytes Ers bs p * hbytes (Share.comp Ers) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

(* the harness identity struct: its public key as a byte buffer (offset 32) and the rest *)
Definition hhs3_p1_F_irest (sh: share) (p: val) (I: mident) : mpred :=
  !! @field_compatible HCS t_mident [] p &&
  (@field_at HCS sh t_mident (DOT HH._priv) (bytes (mi_priv I)) p *
   @field_at HCS sh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p).

Lemma hhs3_p1_F_ib_open sh p I : Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  hbytes sh (mi_pub I) (offset_val 32 p) * hhs3_p1_F_irest sh p I.
Proof.
  intros Hl. unfold hhs3_p1_F_irest, hbytes. rewrite Hl. apply pred_ext.
  - assert_PROP (@field_compatible HCS t_mident [] p) as FC by entailer!.
    unfold_data_at (@data_at HCS sh t_mident _ p).
    rewrite (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. entailer!.
  - Intros. rename H into FC.
    unfold_data_at (@data_at HCS sh t_mident _ p).
    rewrite (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. entailer!.
Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

(* the peer without its handshake and its cookie *)
Definition hhs3_p1_F_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hhs3_p1_F_peer_split sh p P :
  peer_rep sh p P =
  hhs3_p1_F_prest sh p P * hs_rep sh (hs_addr p) (p_hs P) * cookie_rep sh (cookie_addr p) (p_cookie P).
Proof.
  unfold peer_rep, hhs3_p1_F_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

(* the handshake without its state *)
Definition hhs3_p1_F_hrest (sh: share) (h: val) (H: handshake) : mpred :=
   field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
   field_at sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
   field_at sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
   field_at sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
   field_at sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
   field_at sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
   field_at sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
   field_at sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
   field_at sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
   field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h.

Lemma hhs3_p1_F_hs_split sh h H :
  hs_rep sh h H =
  !! hs_ok H && (field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h * hhs3_p1_F_hrest sh h H).
Proof.
  unfold hs_rep, hhs3_p1_F_hrest. apply pred_ext.
  - Intros lk. Exists lk. entailer!.
  - Intros lk. Exists lk. entailer!.
Qed.

(* the cookie: its two keys as byte buffers *)
Definition hhs3_p1_F_ckrest (sh: share) (c: val) (C: cookie) : mpred :=
  !! field_compatible t_cookie [] c &&
  EX lk: val,
  field_at sh t_cookie (DOT I._birthdate) (Vlong (ck_birth C)) c *
  field_at sh t_cookie (DOT I._is_valid) (Val.of_bool (ck_valid C)) c *
  field_at sh t_cookie (DOT I._cookie) (bytes (ck_cookie C)) c *
  field_at sh t_cookie (DOT I._have_sent_mac1) (Val.of_bool (ck_sent C)) c *
  field_at sh t_cookie (DOT I._last_mac1_sent) (bytes (ck_last_mac1 C)) c *
  spacer sh 106 108 c * field_at sh t_cookie (DOT I._lock) lk c.

Lemma hhs3_p1_F_ck_open sh c C :
  cookie_rep sh c C =
  !! cookie_ok C &&
  (hbytes sh (ck_dkey C) (offset_val 42 c) * hbytes sh (ck_mkey C) (offset_val 74 c) * hhs3_p1_F_ckrest sh c C).
Proof.
  unfold cookie_rep, hhs3_p1_F_ckrest, cookie_val. apply pred_ext.
  - Intros lk. pose proof H as (L1 & L2 & L3 & L4).
    assert_PROP (field_compatible t_cookie [] c) as FCc by entailer!.
    unfold hbytes. rewrite L3, L4. rewrite !(@hhs3_p1_F_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cookie _ c).
    rewrite (field_at_data_at sh t_cookie (DOT I._cookie_decryption_key)),
      (field_at_data_at sh t_cookie (DOT I._message_mac1_key)).
    rewrite !field_address_offset by (destruct FCc as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    Exists lk. entailer!.
  - Intros lk. Exists lk. pose proof H as (L1 & L2 & L3 & L4).
    unfold hbytes. rewrite L3, L4. rewrite !(@hhs3_p1_F_tuchar_cs HCS Noise.CS).
    unfold_data_at (data_at _ t_cookie _ c).
    rewrite (field_at_data_at sh t_cookie (DOT I._cookie_decryption_key)),
      (field_at_data_at sh t_cookie (DOT I._message_mac1_key)).
    rewrite !field_address_offset by (destruct H0 as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.

Lemma hhs3_p1_F_hs_close sh h H v : hs_ok H -> hs_state H = v ->
  field_at sh t_hs [StructField I._state] (Vint v) h * hhs3_p1_F_hrest sh h H |-- hs_rep sh h H.
Proof. intros Hok <-. rewrite hhs3_p1_F_hs_split. apply andp_right; [apply prop_right; exact Hok | apply derives_refl]. Qed.

Lemma hhs3_p1_F_ck_close sh c C : cookie_ok C ->
  hbytes sh (ck_dkey C) (offset_val 42 c) * hbytes sh (ck_mkey C) (offset_val 74 c) * hhs3_p1_F_ckrest sh c C
  |-- cookie_rep sh c C.
Proof. intros Hok. rewrite hhs3_p1_F_ck_open. apply andp_right; [apply prop_right; exact Hok | apply derives_refl]. Qed.

Lemma hhs3_p1_F_peer_close sh p P :
  hhs3_p1_F_prest sh p P * hs_rep sh (hs_addr p) (p_hs P) * cookie_rep sh (cookie_addr p) (p_cookie P)
  |-- peer_rep sh p P.
Proof. rewrite hhs3_p1_F_peer_split. apply derives_refl. Qed.
End Fields.

Lemma hhs3_p1_F_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_handshake (Tstruct HC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_handshake hhs3_p1_F_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hhs3_p1_F_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_handshake (Tstruct HC._wg_peer noattr) [StructField HC._handshake] p = hs_addr p.
Proof. intros H. apply hhs3_p1_F_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hhs3_p1_F_hscs : cs_preserve_type Noise.CS W_handshake (@coeq _ _ hhs3_p1_F_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hhs3_p1_F_state sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_hs [StructField prot_repr3.I._state] (Vint v) (hs_addr p) =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state; StructField HC._handshake] (Vint v) p.
Proof.
  intros H.
  change [StructField HC._state; StructField HC._handshake] with ([StructField HC._state] ++ [StructField HC._handshake]).
  rewrite (@field_at_app W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._state] [StructField HC._handshake]
             (Vint v) (Vint v) p (JMeq_refl _)).
  rewrite hhs3_p1_F_hsaddr by exact H.
  exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_handshake hhs3_p1_F_CCE sh t_hs
           [StructField prot_repr3.I._state] (Vint v) (Vint v) (JMeq_refl _) hhs3_p1_F_hscs)).
Qed.

Lemma hhs3_p1_F_label_len l p : Zlength (label_key l p) = 32.
Proof.
  unfold label_key, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
    WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma hhs3_p1_F_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hhs3_p1_F_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p1_F_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p1_SE x25519 gv L FR) hhs3_p1_F
    (overridePost (hhs3_p1_SE x25519 gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_p1_SE, hhs3_Delta, hhs3_R, hhs3_p1_F. simplify_func_tycontext. abbreviate_semax.
  Intros R S a0 f0 l0.
  unfold hhs3_p1_SEsep, hhs3_setup_sep, hhs3_p1_rest, hhs3_globs, hhs3_scr_tmp, hhs3_lvars, hhs3_cnt_temps. cbn [app].
  assert (LpubB: Zlength (mi_pub (hhs3_IB x25519 R)) = 32) by (destruct HH as [X _]; apply X).
  rewrite (hhs3_p1_F_ib_open Tsh (l_ib L) _ LpubB).
  rewrite (hhs3_p1_F_ers_split (mi_pub (hhs3_IB x25519 R))).
  rewrite (hhs3_p1_F_peer_split Tsh (l_pb L)), (hhs3_p1_F_peer_split Tsh (l_pa L)).
  rewrite (hhs3_p1_F_ck_open Tsh (cookie_addr (l_pb L))).
  unfold wg_consts, hhs3_consts. Intros.
  change (hc_const gv HC._x_handshake__M_LABEL_MAC1 mac1_label) with (hbytes Ers mac1_label (gv HC._x_handshake__M_LABEL_MAC1)).
  change (hc_const gv HC._x_handshake__M_LABEL_COOKIE cookie_label) with (hbytes Ers cookie_label (gv HC._x_handshake__M_LABEL_COOKIE)).
  forward_call (gv, Tsh, l_tmp L, Ers, gv HC._x_handshake__M_LABEL_MAC1, mac1_label, offset_val 32 (l_ib L), mi_pub (hhs3_IB x25519 R)).
  set (PB := hhs3_PB0 x25519 R L).
  set (PUB := mi_pub (hhs3_IB x25519 R)).
  assert (EqPM: bytes_eqb (ck_mkey (p_cookie PB)) (label_key mac1_label PUB) = true) by apply hhs3_p1_F_eqb_refl.
  assert (EqPC: bytes_eqb (ck_dkey (p_cookie PB)) (label_key cookie_label PUB) = true) by apply hhs3_p1_F_eqb_refl.
  assert (LcM: Zlength (ck_mkey (p_cookie PB)) = 32) by apply hhs3_p1_F_label_len.
  assert (LcD: Zlength (ck_dkey (p_cookie PB)) = 32) by apply hhs3_p1_F_label_len.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 74 (cookie_addr (l_pb L)), ck_mkey (p_cookie PB), Tsh, l_tmp L,
                  label_key mac1_label PUB).
    rewrite EqPM.
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hhs3_p1_F_hbytes_out Tsh (label_key mac1_label PUB) (l_tmp L)).
  rewrite hhs3_p1_F_label_len.
  forward_call (gv, Tsh, l_tmp L, Ers, gv HC._x_handshake__M_LABEL_COOKIE, cookie_label, offset_val 32 (l_ib L), PUB).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, offset_val 42 (cookie_addr (l_pb L)), ck_dkey (p_cookie PB), Tsh, l_tmp L,
                  label_key cookie_label PUB).
    rewrite EqPC.
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hhs3_p1_F_hbytes_out Tsh (label_key cookie_label PUB) (l_tmp L)).
  rewrite hhs3_p1_F_label_len.
  set (PA := hhs3_PA0 x25519 R L).
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L) /\ @field_compatible Noise.CS t_peer [] (l_pa L)) as FCba.
  { unfold hhs3_p1_F_prest. entailer!. }
  destruct FCba as [FCb FCa].
  rewrite (hhs3_p1_F_hs_split Tsh (hs_addr (l_pb L))), (hhs3_p1_F_hs_split Tsh (hs_addr (l_pa L))). Intros.
  rewrite (hhs3_p1_F_state Tsh (l_pb L) _ FCb), (hhs3_p1_F_state Tsh (l_pa L) _ FCa).
  replace (hs_state (p_hs PB)) with Int.zero by reflexivity.
  replace (hs_state (p_hs PA)) with Int.zero by reflexivity.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward_if (temp HC._t'17 (Vint Int.one)).
    { forward. forward. entailer!. }
    { exfalso. auto. }
    forward_if. { discriminate. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p1_F_state Tsh (l_pb L) Int.zero FCb))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p1_F_state Tsh (l_pa L) Int.zero FCa))).
  sep_apply (hhs3_p1_F_hs_close Tsh (hs_addr (l_pb L)) (p_hs PB) Int.zero H2 eq_refl).
  sep_apply (hhs3_p1_F_hs_close Tsh (hs_addr (l_pa L)) (p_hs PA) Int.zero H3 eq_refl).
  sep_apply (hhs3_p1_F_ck_close Tsh (cookie_addr (l_pb L)) (p_cookie PB) H1).
  sep_apply (hhs3_p1_F_peer_close Tsh (l_pb L) PB).
  sep_apply (hhs3_p1_F_peer_close Tsh (l_pa L) PA).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p1_F_ers_split PUB (offset_val 32 (l_ib L))))).
  Exists R S a0 f0 l0.
  unfold hhs3_p1_SEsep, hhs3_setup_sep, hhs3_p1_rest, hhs3_globs, hhs3_scr_tmp, hhs3_lvars, hhs3_cnt_temps. cbn [app].
  rewrite (hhs3_p1_F_ib_open Tsh (l_ib L) _ LpubB).
  unfold wg_consts, hhs3_consts.
  change (hc_const gv HC._x_handshake__M_LABEL_MAC1 mac1_label) with (hbytes Ers mac1_label (gv HC._x_handshake__M_LABEL_MAC1)).
  change (hc_const gv HC._x_handshake__M_LABEL_COOKIE cookie_label) with (hbytes Ers cookie_label (gv HC._x_handshake__M_LABEL_COOKIE)).
  unfold PUB, PA, PB. entailer!.
Qed.

End Seg.
