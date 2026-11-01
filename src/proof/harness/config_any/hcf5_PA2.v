(* law config_any: main's phase PA2, statements 6..16: ANY prior contents (identity bytes and flag, checker keys, p's precomputed DH and cookie keys), hs_randomize(&p.handshake), peer_randomize_rest(&p), maybe wg_index_hashtable_insert(&it, &p.handshake.entry).
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

#[local] Instance hcf5_pa2_cce : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.
#[local] Instance hcf5_pa2_cceH : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

Lemma hcf5_pa2_fa wg gfs : field_compatible t_dev gfs wg ->
  field_address t_dev gfs wg = offset_val (nested_field_offset t_dev gfs) wg.
Proof. intros. unfold field_address. rewrite if_true by auto. reflexivity. Qed.

Lemma hcf5_pa2_sid sh wg (V: reptype t_sid) : field_compatible t_dev [] wg ->
  data_at sh t_sid V (id_addr wg) = field_at sh t_dev [StructField I._static_identity] V wg.
Proof.
  intros Hfc. rewrite field_at_data_at, hcf5_pa2_fa by auto with field_compatible. reflexivity.
Qed.

Lemma hcf5_pa2_sid_core sh wg (a b: list val) (lk c: val) : field_compatible t_dev [] wg ->
  data_at sh t_sid (a, (b, (lk, c))) (id_addr wg) =
  (data_at sh (tarray tuchar 32) a (offset_val 8 wg) * data_at sh (tarray tuchar 32) b (offset_val 40 wg) *
   (field_at sh t_sid [StructField I._lock] lk (id_addr wg) * spacer sh 69 72 (id_addr wg)) *
   field_at sh t_dev [StructField I._has_identity; StructField I._static_identity] c wg)%logic.
Proof.
  intros Hfc. unfold_data_at (data_at _ _ _ _).
  assert (E: id_addr wg = field_address t_dev [StructField I._static_identity] wg)
    by (rewrite hcf5_pa2_fa by auto with field_compatible; reflexivity).
  pose proof (field_at_app sh t_dev [StructField I._has_identity] [StructField I._static_identity] c c wg (JMeq_refl c)) as X1.
  pose proof (field_at_app sh t_dev [StructField I._static_public] [StructField I._static_identity] a a wg (JMeq_refl a)) as X2.
  pose proof (field_at_app sh t_dev [StructField I._static_private] [StructField I._static_identity] b b wg (JMeq_refl b)) as X3.
  simpl app in X1, X2, X3. change (nested_field_type t_dev [StructField I._static_identity]) with t_sid in X1, X2, X3.
  rewrite <- E in X1, X2, X3. rewrite <- X1, <- X2, <- X3.
  rewrite (field_at_data_at sh t_dev [StructField I._static_public; _]), (field_at_data_at sh t_dev [StructField I._static_private; _]).
  rewrite !hcf5_pa2_fa by auto with field_compatible.
  apply pred_ext; cancel.
Qed.

Lemma hcf5_pa2_fa' t p gfs : field_compatible t gfs p ->
  field_address t gfs p = offset_val (nested_field_offset t gfs) p.
Proof. intros. unfold field_address. rewrite if_true by auto. reflexivity. Qed.

Ltac hcf5_pa2_arr_tac sh root sub T Tsub f v p :=
  intros Hfc;
  let E := fresh "E" in
  assert (E: Tsub = field_address root [StructField sub] p)
    by (rewrite hcf5_pa2_fa' by auto with field_compatible; reflexivity);
  let X := fresh "X" in
  pose proof (field_at_app sh root [StructField f] [StructField sub] v v p (JMeq_refl v)) as X;
  simpl app in X; change (nested_field_type root [StructField sub]) with T in X;
  rewrite <- E in X; rewrite <- X;
  rewrite field_at_data_at, hcf5_pa2_fa' by auto with field_compatible; reflexivity.

Lemma hcf5_pa2_cc_ekey sh wg (v: list val) : field_compatible t_dev [] wg ->
  field_at sh t_cc [StructField I._cookie_encryption_key] v (cc_addr wg) =
  data_at sh (tarray tuchar 32) v (offset_val 112 wg).
Proof. hcf5_pa2_arr_tac sh t_dev I._cookie_checker t_cc (cc_addr wg) I._cookie_encryption_key v wg. Qed.

Lemma hcf5_pa2_cc_mkey sh wg (v: list val) : field_compatible t_dev [] wg ->
  field_at sh t_cc [StructField I._message_mac1_key] v (cc_addr wg) =
  data_at sh (tarray tuchar 32) v (offset_val 144 wg).
Proof. hcf5_pa2_arr_tac sh t_dev I._cookie_checker t_cc (cc_addr wg) I._message_mac1_key v wg. Qed.

Lemma hcf5_pa2_hs_ss sh p (v: list val) : field_compatible t_peer [] p ->
  field_at sh t_hs [StructField I._precomputed_static_static] v (hs_addr p) =
  data_at sh (tarray tuchar 32) v (offset_val 200 p).
Proof. hcf5_pa2_arr_tac sh t_peer I._handshake t_hs (hs_addr p) I._precomputed_static_static v p. Qed.

Lemma hcf5_pa2_ck_dkey sh p (v: list val) : field_compatible t_peer [] p ->
  field_at sh t_cookie [StructField I._cookie_decryption_key] v (cookie_addr p) =
  data_at sh (tarray tuchar 32) v (offset_val 402 p).
Proof. hcf5_pa2_arr_tac sh t_peer I._latest_cookie t_cookie (cookie_addr p) I._cookie_decryption_key v p. Qed.

Lemma hcf5_pa2_ck_mkey sh p (v: list val) : field_compatible t_peer [] p ->
  field_at sh t_cookie [StructField I._message_mac1_key] v (cookie_addr p) =
  data_at sh (tarray tuchar 32) v (offset_val 434 p).
Proof. hcf5_pa2_arr_tac sh t_peer I._latest_cookie t_cookie (cookie_addr p) I._message_mac1_key v p. Qed.

(* ---- the device: identity bytes / flag and checker keys opened ---- *)
Definition hcf5_pa2_drest (sh: share) (wg: val) (D: device) (lkI lkC: val) : mpred :=
  !! field_compatible t_dev [] wg &&
  (field_at sh t_dev [StructField I._dev] (d_dev D) wg *
   (field_at sh t_sid [StructField I._lock] lkI (id_addr wg) * spacer sh 69 72 (id_addr wg)) *
   field_at sh t_cc [StructField I._secret] (bytes (cc_secret (d_cc D))) (cc_addr wg) *
   field_at sh t_cc [StructField I._secret_birthdate] (Vlong (cc_birth (d_cc D))) (cc_addr wg) *
   field_at sh t_cc [StructField I._secret_lock] lkC (cc_addr wg) * spacer sh 108 112 (cc_addr wg) *
   field_at sh t_cc [StructField I._device] (cc_dev (d_cc D)) (cc_addr wg) *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg)%logic.

Definition hcf5_pa2_dset (D: device) (pub priv: list byte) (has: bool) (ek mk: list byte) : device :=
  mkDev (d_dev D) (mkId pub priv has) (mkChk (cc_secret (d_cc D)) ek mk (cc_birth (d_cc D)) (cc_dev (d_cc D)))
    (d_ptab D) (d_itab D).

Lemma hcf5_pa2_cc_core sh wg (s e m: list val) (bd lk dv: val) : field_compatible t_dev [] wg ->
  data_at sh t_cc (s, (e, (m, (bd, (lk, dv))))) (cc_addr wg) =
  (field_at sh t_cc [StructField I._secret] s (cc_addr wg) *
   data_at sh (tarray tuchar 32) e (offset_val 112 wg) * data_at sh (tarray tuchar 32) m (offset_val 144 wg) *
   field_at sh t_cc [StructField I._secret_birthdate] bd (cc_addr wg) *
   field_at sh t_cc [StructField I._secret_lock] lk (cc_addr wg) * spacer sh 108 112 (cc_addr wg) *
   field_at sh t_cc [StructField I._device] dv (cc_addr wg))%logic.
Proof.
  intros Hfc. unfold_data_at (data_at _ _ _ _).
  rewrite hcf5_pa2_cc_ekey, hcf5_pa2_cc_mkey by auto. apply pred_ext; cancel.
Qed.

Lemma hcf5_pa2_dev_open sh wg D : device_rep sh wg D |--
  EX lkI: val, EX lkC: val,
  !! (id_ok (d_id D) /\ cc_ok (d_cc D)) &&
  (hcf5_pa2_drest sh wg D lkI lkC *
   data_at sh (tarray tuchar 32) (bytes (id_pub (d_id D))) (offset_val 8 wg) *
   data_at sh (tarray tuchar 32) (bytes (id_priv (d_id D))) (offset_val 40 wg) *
   field_at sh t_dev [StructField I._has_identity; StructField I._static_identity] (Val.of_bool (id_has (d_id D))) wg *
   data_at sh (tarray tuchar 32) (bytes (cc_ekey (d_cc D))) (offset_val 112 wg) *
   data_at sh (tarray tuchar 32) (bytes (cc_mkey (d_cc D))) (offset_val 144 wg))%logic.
Proof.
  unfold device_rep, identity_rep, checker_rep. Intros lkI lkC.
  rewrite hcf5_pa2_sid_core, hcf5_pa2_cc_core by auto.
  Exists lkC lkI. unfold hcf5_pa2_drest. entailer!.
Qed.

Lemma hcf5_pa2_dev_close sh wg D lkI lkC pub priv has ek mk :
  Zlength pub = 32 -> Zlength priv = 32 -> Zlength ek = 32 -> Zlength mk = 32 -> Zlength (cc_secret (d_cc D)) = 32 ->
  (hcf5_pa2_drest sh wg D lkI lkC *
   data_at sh (tarray tuchar 32) (bytes pub) (offset_val 8 wg) *
   data_at sh (tarray tuchar 32) (bytes priv) (offset_val 40 wg) *
   field_at sh t_dev [StructField I._has_identity; StructField I._static_identity] (Val.of_bool has) wg *
   data_at sh (tarray tuchar 32) (bytes ek) (offset_val 112 wg) *
   data_at sh (tarray tuchar 32) (bytes mk) (offset_val 144 wg))%logic
  |-- device_rep sh wg (hcf5_pa2_dset D pub priv has ek mk).
Proof.
  intros H1 H2 H3 H4 H5. unfold hcf5_pa2_drest. Intros.
  unfold device_rep, identity_rep, checker_rep, hcf5_pa2_dset; cbn [d_dev d_id d_cc d_ptab d_itab id_pub id_priv id_has
    cc_secret cc_ekey cc_mkey cc_birth cc_dev].
  Exists lkC lkI.
  rewrite hcf5_pa2_sid_core, hcf5_pa2_cc_core by auto.
  unfold id_ok, cc_ok; cbn [id_pub id_priv cc_secret cc_ekey cc_mkey].
  entailer!.
Qed.

(* ---- the peer: precomputed DH and cookie keys opened ---- *)
Definition hcf5_pa2_hsrest (sh: share) (h: val) (H: handshake) : mpred := (
  field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h *
  field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
  field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
  field_at sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
  field_at sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
  field_at sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
  field_at sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
  field_at sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
  field_at sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
  field_at sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
  field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
  (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h)%logic.

Definition hcf5_pa2_ckrest (sh: share) (c: val) (C: cookie) (lk: val) : mpred := (
  field_at sh t_cookie [StructField I._birthdate] (Vlong (ck_birth C)) c *
  field_at sh t_cookie [StructField I._is_valid] (Val.of_bool (ck_valid C)) c *
  field_at sh t_cookie [StructField I._cookie] (bytes (ck_cookie C)) c *
  field_at sh t_cookie [StructField I._have_sent_mac1] (Val.of_bool (ck_sent C)) c *
  field_at sh t_cookie [StructField I._last_mac1_sent] (bytes (ck_last_mac1 C)) c *
  spacer sh 106 108 c * field_at sh t_cookie [StructField I._lock] lk c)%logic.

Definition hcf5_pa2_prest (sh: share) (p: val) (P: peer) (lk: val) : mpred :=
  !! (field_compatible t_peer [] p /\ hs_ok (p_hs P) /\ cookie_ok (p_cookie P)) &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hcf5_pa2_hsrest sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   hcf5_pa2_ckrest sh (cookie_addr p) (p_cookie P) lk *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Definition hcf5_pa2_pset (P: peer) (ss dk mk: list byte) : peer :=
  let H := p_hs P in let C := p_cookie P in
  mkPeer (p_device P) (p_dead P) (p_cur P) (p_prev P) (p_next P)
    (mkHS (hs_state H) (hs_lic H) (hs_sid H) (hs_eph H) (hs_rstatic H) (hs_reph H) ss (hs_psk H) (hs_hash H)
          (hs_ck H) (hs_ts H) (hs_rindex H))
    (p_lsh P)
    (mkCookie (ck_birth C) (ck_valid C) (ck_cookie C) (ck_sent C) (ck_last_mac1 C) dk mk)
    (p_refs P) (p_id P) (p_pknext P).

Lemma hcf5_pa2_ck_core sh p C lk : field_compatible t_peer [] p ->
  data_at sh t_cookie (cookie_val C lk) (cookie_addr p) =
  (hcf5_pa2_ckrest sh (cookie_addr p) C lk *
   data_at sh (tarray tuchar 32) (bytes (ck_dkey C)) (offset_val 402 p) *
   data_at sh (tarray tuchar 32) (bytes (ck_mkey C)) (offset_val 434 p))%logic.
Proof.
  intros Hfc. unfold cookie_val. unfold_data_at (data_at _ _ _ _).
  rewrite hcf5_pa2_ck_dkey, hcf5_pa2_ck_mkey by auto. unfold hcf5_pa2_ckrest. apply pred_ext; cancel.
Qed.

Lemma hcf5_pa2_peer_open sh p P : peer_rep sh p P |--
  EX lk: val,
  (hcf5_pa2_prest sh p P lk *
   data_at sh (tarray tuchar 32) (bytes (hs_ss (p_hs P))) (offset_val 200 p) *
   data_at sh (tarray tuchar 32) (bytes (ck_dkey (p_cookie P))) (offset_val 402 p) *
   data_at sh (tarray tuchar 32) (bytes (ck_mkey (p_cookie P))) (offset_val 434 p))%logic.
Proof.
  unfold peer_rep, hs_rep, cookie_rep. Intros lk lkh.
  rewrite hcf5_pa2_hs_ss, hcf5_pa2_ck_core by auto.
  Exists lk. unfold hcf5_pa2_prest, hcf5_pa2_hsrest. Exists lkh. entailer!.
Qed.

Lemma hcf5_pa2_peer_close sh p P lk ss dk mk :
  Zlength ss = 32 -> Zlength dk = 32 -> Zlength mk = 32 ->
  (hcf5_pa2_prest sh p P lk *
   data_at sh (tarray tuchar 32) (bytes ss) (offset_val 200 p) *
   data_at sh (tarray tuchar 32) (bytes dk) (offset_val 402 p) *
   data_at sh (tarray tuchar 32) (bytes mk) (offset_val 434 p))%logic
  |-- peer_rep sh p (hcf5_pa2_pset P ss dk mk).
Proof.
  intros H1 H2 H3. unfold hcf5_pa2_prest, hcf5_pa2_hsrest. Intros lkh.
  unfold peer_rep, hs_rep, cookie_rep, hcf5_pa2_pset.
  Exists lk lkh.
  rewrite hcf5_pa2_hs_ss, hcf5_pa2_ck_core by auto.
  unfold hcf5_pa2_ckrest; cbn [p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie
    p_refs p_id p_pknext hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex
    ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey].
  unfold hs_ok, cookie_ok in *; cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts ck_cookie ck_last_mac1
    ck_dkey ck_mkey] in *.
  entailer!.
Qed.

End NoiseCS.

Lemma hcf5_pa2_arrW sh (v: list val) p :
  @data_at Noise.CS sh (tarray tuchar 32) v p = @data_at W_config_any sh (tarray tuchar 32) v p.
Proof.
  apply equal_f. apply (@data_at_change_composite Noise.CS W_config_any _ sh (tarray tuchar 32) v v (JMeq_refl _)).
  prove_cs_preserve_type.
Qed.

Lemma hcf5_pa2_nd sh bs p : Zlength bs = 32 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_config_any sh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) p =
  @data_at Noise.CS sh (tarray tuchar 32) (bytes (map Byte.repr bs)) p.
Proof.
  intros Hn Hb. rewrite hcf5_pa2_arrW. f_equal. unfold bytes. rewrite map_map.
  clear Hn. induction Hb; simpl; [reflexivity |]. f_equal; [| assumption].
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia). reflexivity.
Qed.

Lemma hcf5_pa2_hasW sh v wg :
  @field_at Noise.CS sh t_dev [StructField I._has_identity; StructField I._static_identity] v wg =
  @field_at W_config_any sh t_dev [StructField I._has_identity; StructField I._static_identity] v wg.
Proof.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_config_any _ sh t_dev); [apply JMeq_refl | reflexivity].
Qed.

(* p's handshake entry joins the empty pool *)
Lemma hcf5_pa2_entry_fold sht tab sh a E :
  writable_share sh ->
  itable sht tab (mkT [] []) * entry_out sh a E |-- itable sht tab (mkT [(a, sh, E)] []).
Proof.
  intros Hw. unfold itable, itable_wf. simpl. Intros. unfold entry_out.
  unfold vin. simpl. entailer!.
  split; [intros x [] | constructor; [intros [] | constructor]].
Qed.

Definition hcf5_pa2_T0 (p: val) (T: tstate) : Prop :=
  exists i, t_D T = [(hs_addr p, Tsh, mkEntry p IDX_HANDSHAKE i)].

Lemma hcf5_pa2_T0_insert p idx :
  hcf5_pa2_T0 p (t_insert (mkT [(hs_addr p, Tsh, mkEntry p IDX_HANDSHAKE Int.zero)] []) (hs_addr p) idx).
Proof.
  exists idx. unfold t_insert, t_set_index, t_entry, t_upd. simpl.
  destruct (EqDec_val (hs_addr p) (hs_addr p)) as [_|n]; [| congruence]. simpl.
  destruct (EqDec_val (hs_addr p) (hs_addr p)) as [_|n]; [| congruence]. reflexivity.
Qed.

Lemma hcf5_pa2_T_ok L T : hcf5_pa2_T0 (l_p L) T -> hcf5_T_ok L [] false T.
Proof.
  intros [i Hi]. unfold hcf5_T_ok, hcf5_tsh, t_entry_d, t_entry, hcf5_qs. rewrite Hi. simpl.
  destruct (EqDec_val (hs_addr (l_p L)) (hs_addr (l_p L))) as [_|n]; [| congruence].
  repeat split; auto; discriminate.
Qed.

Section PA2.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_PA2_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_SA1 x25519 gv L FR) hcf5_PA2
    (overridePost (hcf5_SA gv L FR) (hcf5_R gv)).
Proof.
  intros HH. unfold hcf5_SA1, hcf5_Delta, hcf5_R, hcf5_PA2. simplify_func_tycontext. abbreviate_semax.
  Intros R S w.
  unfold hcf5_lvars, hcf5_pre, hcf5_globs; cbn [app].
  sep_apply (hcf5_pa2_dev_open Tsh (l_w L) (hcf5_D0 x25519 R L)). Intros lkI lkC.
  rewrite !hcf5_pa2_arrW, hcf5_pa2_hasW.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes (id_pub (d_id (hcf5_D0 x25519 R L)))) (offset_val 8 (l_w L))).
  forward_call (offset_val 8 (l_w L), 32, Tsh). Intros b1.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes (id_priv (d_id (hcf5_D0 x25519 R L)))) (offset_val 40 (l_w L))).
  forward_call (offset_val 40 (l_w L), 32, Tsh). Intros b2.
  forward_call tt. Intros b3.
  forward.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes (cc_ekey (d_cc (hcf5_D0 x25519 R L)))) (offset_val 112 (l_w L))).
  forward_call (offset_val 112 (l_w L), 32, Tsh). Intros b4.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes (cc_mkey (d_cc (hcf5_D0 x25519 R L)))) (offset_val 144 (l_w L))).
  forward_call (offset_val 144 (l_w L), 32, Tsh). Intros b5.
  (* refold the device *)
  set (has := negb (Int.eq (Int.and (Int.repr b3) (Int.repr 1)) Int.zero)).
  replace (Vint (if Int.eq (Int.and (Int.repr b3) (Int.repr 1)) Int.zero then Int.zero else Int.one))
    with (Val.of_bool has) by (unfold has; destruct (Int.eq _ _); reflexivity).
  rewrite <- hcf5_pa2_hasW.
  rewrite (hcf5_pa2_nd Tsh b1), (hcf5_pa2_nd Tsh b2), (hcf5_pa2_nd Tsh b4), (hcf5_pa2_nd Tsh b5) by assumption.
  sep_apply (hcf5_pa2_dev_close Tsh (l_w L) (hcf5_D0 x25519 R L) lkI lkC (map Byte.repr b1) (map Byte.repr b2) has
               (map Byte.repr b4) (map Byte.repr b5)); try (rewrite Zlength_map; assumption).
  { destruct H3 as (? & _); assumption. }
  set (D1 := hcf5_pa2_dset (hcf5_D0 x25519 R L) (map Byte.repr b1) (map Byte.repr b2) has (map Byte.repr b4) (map Byte.repr b5)).
  (* the peer's precomputed DH and cookie keys *)
  sep_apply (hcf5_pa2_peer_open Tsh (l_p L) (hcf5_P0 x25519 R L)). Intros lkP.
  rewrite !hcf5_pa2_arrW.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes (hs_ss (p_hs (hcf5_P0 x25519 R L)))) (offset_val 200 (l_p L))).
  forward_call (offset_val 200 (l_p L), 32, Tsh). Intros b6.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes (ck_dkey (p_cookie (hcf5_P0 x25519 R L)))) (offset_val 402 (l_p L))).
  forward_call (offset_val 402 (l_p L), 32, Tsh). Intros b7.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes (ck_mkey (p_cookie (hcf5_P0 x25519 R L)))) (offset_val 434 (l_p L))).
  forward_call (offset_val 434 (l_p L), 32, Tsh). Intros b8.
  rewrite (hcf5_pa2_nd Tsh b6), (hcf5_pa2_nd Tsh b7), (hcf5_pa2_nd Tsh b8) by assumption.
  sep_apply (hcf5_pa2_peer_close Tsh (l_p L) (hcf5_P0 x25519 R L) lkP (map Byte.repr b6) (map Byte.repr b7)
               (map Byte.repr b8)); try (rewrite Zlength_map; assumption).
  set (P1 := hcf5_pa2_pset (hcf5_P0 x25519 R L) (map Byte.repr b6) (map Byte.repr b7) (map Byte.repr b8)).
  (* hs_randomize(&p.handshake) *)
  forward_call (Tsh, l_p L, P1, false).
  Intros vret. destruct vret as [[[[[[[st lic] eph] reph] hash] ck] ts] ri]; simpl fst in *; simpl snd in *.
  set (P2 := p_set_hs P1 (hs_randomized (p_hs P1) st lic eph reph hash ck ts ri)).
  (* peer_randomize_rest(&p) *)
  forward_call (Tsh, l_p L, P2).
  Intros vret. destruct vret as [[[[[[dead lsh] valid] birth] cki] sent] mac1]; simpl fst in *; simpl snd in *.
  set (P3 := p_rest_randomized P2 dead lsh valid birth cki sent mac1).
  forward_call tt. Intros b9.
  sep_apply (hcf5_pa2_entry_fold Tsh (l_it L) Tsh (hs_addr (l_p L)) (mkEntry (l_p L) IDX_HANDSHAKE Int.zero)
               writable_share_top).
  forward_if (EX T: tstate, EX S1: shim,
    PROPx [hcf5_pa2_T0 (l_p L) T; s_boot S1 = r_now R]
    (LOCALx (temp HF._now (Vlong (r_now R)) :: hcf5_lvars gv L)
    (SEPx ([device_rep Tsh (l_w L) D1; itable Tsh (l_it L) T; ptable Tsh (l_pt L) (l_p L); peer_rep Tsh (l_p L) P3;
            hbytes Tsh (r_raw0 R) (l_raw0 L); hbytes Tsh (r_pub R) (l_pub L)] ++
           hcf5_globs gv S1 w FR ++ hcf5_pre L ++ [hcf5_X0 L])))).
  - forward_call (gv, S, w, Tsh, l_it L, mkT [(hs_addr (l_p L), Tsh, mkEntry (l_p L) IDX_HANDSHAKE Int.zero)] [],
                  hs_addr (l_p L), @None (share * entry)).
    { change (raw_rep (hs_addr (l_p L)) None) with emp. rewrite emp_sepcon. cancel. }
    { simpl; auto. }
    change (raw_add _ (hs_addr (l_p L)) None)
      with (mkT [(hs_addr (l_p L), Tsh, mkEntry (l_p L) IDX_HANDSHAKE Int.zero)] []). Intros idx.
    Exists (t_insert (mkT [(hs_addr (l_p L), Tsh, mkEntry (l_p L) IDX_HANDSHAKE Int.zero)] []) (hs_addr (l_p L)) idx)
      (shim_u32 S idx).
    unfold hcf5_lvars, hcf5_pre, hcf5_globs; cbn [app].
    entailer!. apply hcf5_pa2_T0_insert.
  - forward.
    Exists (mkT [(hs_addr (l_p L), Tsh, mkEntry (l_p L) IDX_HANDSHAKE Int.zero)] []) S.
    unfold hcf5_lvars, hcf5_pre, hcf5_globs; cbn [app].
    entailer!. exists Int.zero. reflexivity.
  - Intros T S1.
    unfold hcf5_SA. Exists R S1 w D1 P3 T.
    unfold hcf5_lvars, hcf5_pre, hcf5_globs; cbn [app].
    entailer!.
    split; [| split]; [| | apply hcf5_pa2_T_ok; assumption].
    + unfold hcf5_dok; repeat split; reflexivity.
    + unfold hcf5_pok; repeat split; reflexivity.
Qed.

End PA2.
