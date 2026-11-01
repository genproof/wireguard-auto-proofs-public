(* law config_any: main's phase P6, statements 86..92: step 6: w's checker secret / birthdate / device ANY, wg_cookie_checker_init(&w.cookie_checker, &w), the edits of ds.
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

#[local] Instance hcf5_p6_cceN : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.
#[local] Instance hcf5_p6_cceH : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.
#[local] Instance hcf5_p6_cceK : change_composite_env CKS W_config_any.
Proof. make_cs_preserve CKS W_config_any. Defined.

Section NoiseCS6.
#[local] Existing Instance Noise.CS.

Lemma hcf5_p6_fa wg gfs : field_compatible t_dev gfs wg ->
  field_address t_dev gfs wg = offset_val (nested_field_offset t_dev gfs) wg.
Proof. intros. unfold field_address. rewrite if_true by auto. reflexivity. Qed.

Ltac hcf5_p6_fld_tac sh wg f v :=
  intros Hfc;
  let E := fresh "E" in
  assert (E: cc_addr wg = field_address t_dev [StructField I._cookie_checker] wg)
    by (rewrite hcf5_p6_fa by auto with field_compatible; reflexivity);
  rewrite E;
  let X := fresh "X" in
  pose proof (field_at_app sh t_dev [StructField f] [StructField I._cookie_checker] v v wg (JMeq_refl v)) as X;
  simpl app in X; exact (eq_sym X).

Lemma hcf5_p6_cc_birth sh wg (v: val) : field_compatible t_dev [] wg ->
  field_at sh t_cc [StructField I._secret_birthdate] v (cc_addr wg) =
  field_at sh t_dev [StructField I._secret_birthdate; StructField I._cookie_checker] v wg.
Proof. hcf5_p6_fld_tac sh wg I._secret_birthdate v. Qed.

Lemma hcf5_p6_cc_dev sh wg (v: val) : field_compatible t_dev [] wg ->
  field_at sh t_cc [StructField I._device] v (cc_addr wg) =
  field_at sh t_dev [StructField I._device; StructField I._cookie_checker] v wg.
Proof. hcf5_p6_fld_tac sh wg I._device v. Qed.

Lemma hcf5_p6_cc_sec' sh wg (v: list val) : field_compatible t_dev [] wg ->
  field_at sh t_cc [StructField I._secret] v (cc_addr wg) =
  field_at sh t_dev [StructField I._secret; StructField I._cookie_checker] v wg.
Proof. hcf5_p6_fld_tac sh wg I._secret v. Qed.

Lemma hcf5_p6_cc_secret sh wg (v: list val) : field_compatible t_dev [] wg ->
  field_at sh t_cc [StructField I._secret] v (cc_addr wg) =
  data_at sh (tarray tuchar 32) v (offset_val 80 wg).
Proof.
  intros Hfc. rewrite (hcf5_p6_cc_sec' sh wg v Hfc).
  rewrite field_at_data_at, hcf5_p6_fa by auto with field_compatible. reflexivity.
Qed.

(* the device without its checker *)
Definition hcf5_p6_drest (sh: share) (wg: val) (D: device) : mpred :=
  (field_at sh t_dev [StructField I._dev] (d_dev D) wg *
   identity_rep sh (id_addr wg) (d_id D) *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg)%logic.

Lemma hcf5_p6_dev_open sh wg D :
  device_rep sh wg D =
  (!! field_compatible t_dev [] wg && (checker_rep sh (cc_addr wg) (d_cc D) * hcf5_p6_drest sh wg D))%logic.
Proof. unfold device_rep, hcf5_p6_drest. apply pred_ext; entailer!. Qed.

(* the checker's fields: the secret as a byte array, birthdate and device at the device's root *)
Definition hcf5_p6_ckeep (sh: share) (c: val) (ek mk: list byte) (lk: val) : mpred :=
  (field_at sh t_cc [StructField I._cookie_encryption_key] (bytes ek) c *
   field_at sh t_cc [StructField I._message_mac1_key] (bytes mk) c *
   field_at sh t_cc [StructField I._secret_lock] lk c * spacer sh 108 112 c)%logic.

Lemma hcf5_p6_cc_open sh wg CC : field_compatible t_dev [] wg ->
  checker_rep sh (cc_addr wg) CC |--
  EX lk: val, !! cc_ok CC &&
  (data_at sh (tarray tuchar 32) (bytes (cc_secret CC)) (offset_val 80 wg) *
   field_at sh t_dev [StructField I._secret_birthdate; StructField I._cookie_checker] (Vlong (cc_birth CC)) wg *
   field_at sh t_dev [StructField I._device; StructField I._cookie_checker] (cc_dev CC) wg *
   hcf5_p6_ckeep sh (cc_addr wg) (cc_ekey CC) (cc_mkey CC) lk)%logic.
Proof.
  intros Hfc. unfold checker_rep. Intros lk. Exists lk.
  unfold_data_at (data_at _ _ _ _).
  rewrite (hcf5_p6_cc_secret sh wg _ Hfc).
  rewrite (hcf5_p6_cc_birth sh wg _ Hfc).
  rewrite (hcf5_p6_cc_dev sh wg _ Hfc).
  unfold hcf5_p6_ckeep. entailer!.
Qed.

Lemma hcf5_p6_cc_pre sh wg : field_compatible t_dev [] wg ->
  data_at_ sh (tarray tuchar 32) (offset_val 80 wg) *
  field_at_ sh t_dev [StructField I._secret_birthdate; StructField I._cookie_checker] wg *
  field_at_ sh t_dev [StructField I._device; StructField I._cookie_checker] wg |--
  field_at_ sh t_cc [StructField I._secret] (cc_addr wg) *
  field_at_ sh t_cc [StructField I._secret_birthdate] (cc_addr wg) *
  field_at_ sh t_cc [StructField I._device] (cc_addr wg).
Proof.
  intros Hfc. unfold field_at_.
  rewrite (hcf5_p6_cc_secret sh wg _ Hfc).
  rewrite (hcf5_p6_cc_birth sh wg _ Hfc).
  rewrite (hcf5_p6_cc_dev sh wg _ Hfc).
  unfold data_at_, field_at_. cancel.
Qed.

Lemma hcf5_p6_dev_close sh wg D CC :
  (!! field_compatible t_dev [] wg && (checker_rep sh (cc_addr wg) CC * hcf5_p6_drest sh wg D))%logic
  |-- device_rep sh wg (dev_set_cc D CC).
Proof. rewrite hcf5_p6_dev_open. apply derives_refl. Qed.

End NoiseCS6.

Lemma hcf5_p6_arrW sh (v: list val) p :
  @data_at Noise.CS sh (tarray tuchar 32) v p = @data_at W_config_any sh (tarray tuchar 32) v p.
Proof.
  apply equal_f. apply (@data_at_change_composite Noise.CS W_config_any _ sh (tarray tuchar 32) v v (JMeq_refl _)).
  prove_cs_preserve_type.
Qed.

Lemma hcf5_p6_birthW sh (v: val) wg :
  @field_at Noise.CS sh t_dev [StructField I._secret_birthdate; StructField I._cookie_checker] v wg =
  @field_at W_config_any sh t_dev [StructField I._secret_birthdate; StructField I._cookie_checker] v wg.
Proof.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_config_any _ sh t_dev); [apply JMeq_refl | reflexivity].
Qed.

Lemma hcf5_p6_devW sh (v: val) wg :
  @field_at Noise.CS sh t_dev [StructField I._device; StructField I._cookie_checker] v wg =
  @field_at W_config_any sh t_dev [StructField I._device; StructField I._cookie_checker] v wg.
Proof.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_config_any _ sh t_dev); [apply JMeq_refl | reflexivity].
Qed.

(* the shim's random log *)
Definition hcf5_p6_srest (gv: globals) (S: shim) : mpred :=
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic.

Lemma hcf5_p6_hb_W sh bs p : hbytes sh bs p = @data_at W_config_any sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof.
  unfold hbytes. apply equal_f.
  apply (@data_at_change_composite HCS W_config_any _ sh (tarray tuchar (Zlength bs))); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p6_core_open gv S :
  shim_core gv S = (!! shim_ok S && (hbytes Ews (s_log S) (gv _wg_shim_random_log) * hcf5_p6_srest gv S))%logic.
Proof.
  unfold shim_core, hcf5_p6_srest.
  apply pred_ext; Intros; pose proof H as [HL _]; rewrite hcf5_p6_hb_W, HL, <- hcf5_p6_arrW; entailer!.
Qed.

Lemma hcf5_p6_log S r : Zlength r = 32 -> s_log (shim_draw S r) = r.
Proof.
  intros HL. unfold shim_draw; simpl. rewrite HL. change (Z.min 32 32) with 32.
  rewrite sublist_same by auto. rewrite sublist_nil. apply app_nil_r.
Qed.

Lemma hcf5_p6_cc_preW sh wg (v: list val) (v1 v2: val) : @field_compatible Noise.CS t_dev [] wg ->
  (@data_at W_config_any sh (tarray tuchar 32) v (offset_val 80 wg) *
   @field_at W_config_any sh t_dev [StructField I._secret_birthdate; StructField I._cookie_checker] v1 wg *
   @field_at W_config_any sh t_dev [StructField I._device; StructField I._cookie_checker] v2 wg)%logic |--
  (@field_at_ Noise.CS sh t_cc [StructField I._secret] (cc_addr wg) *
   @field_at_ Noise.CS sh t_cc [StructField I._secret_birthdate] (cc_addr wg) *
   @field_at_ Noise.CS sh t_cc [StructField I._device] (cc_addr wg))%logic.
Proof.
  intros Hfc. rewrite <- hcf5_p6_arrW, <- hcf5_p6_birthW, <- hcf5_p6_devW.
  eapply derives_trans; [| apply (hcf5_p6_cc_pre sh wg Hfc)].
  apply sepcon_derives; [apply sepcon_derives |]; [apply data_at_data_at_ | apply field_at_field_at_ | apply field_at_field_at_].
Qed.

Lemma hcf5_p6_hout_len sh n p (A: list byte) : Zlength A = n -> hout sh n p = hout sh (Zlength A) p.
Proof. intros ->. reflexivity. Qed.

Lemma hcf5_p6_hb_W32 sh bs p : Zlength bs = 32 ->
  hbytes sh bs p = @data_at W_config_any sh (tarray tuchar 32) (bytes bs) p.
Proof. intros HL. rewrite hcf5_p6_hb_W, HL. reflexivity. Qed.

Lemma hcf5_p6_ds_W sh v p : @data_at CKS sh t_devsnap v p = @data_at W_config_any sh t_devsnap v p.
Proof.
  apply equal_f.
  apply (@data_at_change_composite CKS W_config_any _ sh t_devsnap); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Definition hcf5_p6_setc (D: device) (s: list byte) (b: int64) (d: val) : device :=
  dev_set_cc D (mkChk s (cc_ekey (d_cc D)) (cc_mkey (d_cc D)) b d).

Lemma hcf5_p6_dsec sh D h p s :
  @data_at W_config_any sh t_devsnap (devsnap_val D h) p |--
  @data_at_ W_config_any sh (tarray tuchar 32) (@field_address W_config_any t_devsnap (DOT HF._secret) p) *
  (@data_at W_config_any sh (tarray tuchar 32) (bytes s) (@field_address W_config_any t_devsnap (DOT HF._secret) p) -*
   @data_at W_config_any sh t_devsnap (devsnap_val (hcf5_p6_setc D s (cc_birth (d_cc D)) (cc_dev (d_cc D))) h) p).
Proof.
  assert_PROP (@field_compatible W_config_any t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HF._secret)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - rewrite field_at_data_at. apply sepcon_derives; [apply data_at_data_at_ |].
    apply (allp_left _ (bytes s)). apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hcf5_p6_dbirth sh D h p b :
  @data_at W_config_any sh t_devsnap (devsnap_val D h) p |--
  @field_at_ W_config_any sh t_devsnap (DOT HF._secret_birthdate) p *
  (@field_at W_config_any sh t_devsnap (DOT HF._secret_birthdate) (Vlong b) p -*
   @data_at W_config_any sh t_devsnap (devsnap_val (hcf5_p6_setc D (cc_secret (d_cc D)) b (cc_dev (d_cc D))) h) p).
Proof.
  assert_PROP (@field_compatible W_config_any t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HF._secret_birthdate)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - apply sepcon_derives; [apply field_at_field_at_ |].
    apply (allp_left _ (Vlong b)). apply wand_derives; [apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hcf5_p6_ddev sh D h p d :
  @data_at W_config_any sh t_devsnap (devsnap_val D h) p |--
  @field_at_ W_config_any sh t_devsnap (DOT HF._checker_device) p *
  (@field_at W_config_any sh t_devsnap (DOT HF._checker_device) d p -*
   @data_at W_config_any sh t_devsnap (devsnap_val (hcf5_p6_setc D (cc_secret (d_cc D)) (cc_birth (d_cc D)) d) h) p).
Proof.
  assert_PROP (@field_compatible W_config_any t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HF._checker_device)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - apply sepcon_derives; [apply field_at_field_at_ |].
    apply (allp_left _ d). apply wand_derives; [apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Section P6.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_P6_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_SX5 x25519 gv L FR) hcf5_P6
    (overridePost (hcf5_SX5 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HH. unfold hcf5_SX5, hcf5_Delta, hcf5_R, hcf5_P6. simplify_func_tycontext. abbreviate_semax.
  Intros R S w D P T KE. Intros D0 sn0 P0 r0 S0 w0 h0 RAW H.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars, hcf5_X5. cbn [app].
  Intros. rename H0 into HPx, H1 into HQ, H2 into Hinv, H3 into Hsame.
  pose proof Hsame as (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh0).
  apply hcf5_dev_eqb_eq in Hdev. destruct Hdev as [-> _].
  rewrite hcf5_p6_dev_open. Intros. rename H0 into Hfc.
  sep_apply (hcf5_p6_cc_open Tsh (l_w L) (d_cc D) Hfc). Intros lk. rename H0 into Hcc.
  rewrite hcf5_p6_arrW, hcf5_p6_birthW, hcf5_p6_devW.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes (cc_secret (d_cc D))) (offset_val 80 (l_w L))).
  forward_call (offset_val 80 (l_w L), 32, Tsh). Intros bs.
  forward_call tt. Intros vb.
  forward.
  forward_call tt. Intros u8.
  match goal with |- semax _ (PROPx ?Pp (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (EX vd: val, PROPx (is_pointer_or_null vd :: Pp) (LOCALx (temp HF._t'90 vd :: Q) (SEPx Rs)))
  end.
  - forward. Exists (l_w L). entailer!.
  - forward. Exists nullval. entailer!.
  - Intros vd. forward.
    sep_apply (hcf5_p6_cc_preW Tsh (l_w L) (map (fun b : Z => Vint (Int.repr b)) bs) (Vlong vb) vd Hfc).
    unfold hcf5_p6_ckeep. Intros.
    forward_call (gv, S, w, Tsh, cc_addr (l_w L), cc_ekey (d_cc D), cc_mkey (d_cc D), l_w L).
    { unfold cc_ok in Hcc; tauto. }
    Intros r. rename H3 into Hlr.
    set (D' := dev_set_cc D (mkChk r (cc_ekey (d_cc D)) (cc_mkey (d_cc D)) (s_boot S) (l_w L))).
    gather_SEP (checker_rep _ _ _) (hcf5_p6_drest _ _ _).
    replace_SEP 0 (device_rep Tsh (l_w L) D').
    { unfold D'. rewrite hcf5_p6_dev_open. entailer!. apply derives_refl. }
    unfold shim_state4. rewrite hcf5_p6_core_open. Intros.
    rewrite (hcf5_p6_log S r Hlr).
    rewrite hcf5_p6_ds_W.
    assert_PROP (field_compatible t_devsnap [] (l_ds L)) as Hfds by entailer!.
    sep_apply (hcf5_p6_dsec Tsh D (l_p L) (l_ds L) r).
    rewrite <- (hcf5_conv_bytes Tsh 32 (field_address t_devsnap (DOT HF._secret) (l_ds L))).
    rewrite (hcf5_p6_hout_len Tsh 32 _ r Hlr).
    forward_call (Tsh, field_address t_devsnap (DOT HF._secret) (l_ds L), Ews, gv HF._wg_shim_random_log, r).
    { rewrite Hlr. entailer!. simpl. rewrite !field_address_offset by auto with field_compatible. reflexivity. }
    { change (gv HF._wg_shim_random_log) with (gv _wg_shim_random_log). cancel. }
    change (gv HF._wg_shim_random_log) with (gv _wg_shim_random_log).
    rewrite (hcf5_p6_hb_W32 Tsh r (field_address t_devsnap (DOT HF._secret) (l_ds L)) Hlr).
    set (D1 := hcf5_p6_setc D r (cc_birth (d_cc D)) (cc_dev (d_cc D))).
    sep_apply (wand_frame_elim (@data_at W_config_any Tsh (tarray tuchar 32) (bytes r)
                 (field_address t_devsnap (DOT HF._secret) (l_ds L)))
                 (@data_at W_config_any Tsh t_devsnap (devsnap_val D1 (l_p L)) (l_ds L))).
    sep_apply (hcf5_p6_dbirth Tsh D1 (l_p L) (l_ds L) (r_now R)). Intros.
    forward.
    set (D2 := hcf5_p6_setc D1 (cc_secret (d_cc D1)) (r_now R) (cc_dev (d_cc D1))).
    sep_apply (wand_frame_elim (@field_at W_config_any Tsh t_devsnap (DOT HF._secret_birthdate) (Vlong (r_now R)) (l_ds L))
                 (@data_at W_config_any Tsh t_devsnap (devsnap_val D2 (l_p L)) (l_ds L))).
    sep_apply (hcf5_p6_ddev Tsh D2 (l_p L) (l_ds L) (l_w L)). Intros.
    forward.
    set (D3 := hcf5_p6_setc D2 (cc_secret (d_cc D2)) (cc_birth (d_cc D2)) (l_w L)).
    sep_apply (wand_frame_elim (@field_at W_config_any Tsh t_devsnap (DOT HF._checker_device) (l_w L) (l_ds L))
                 (@data_at W_config_any Tsh t_devsnap (devsnap_val D3 (l_p L)) (l_ds L))).
    pose proof Hinv as (Ha & Hb & Hc & (Hd1 & Hd2 & Hd3 & Hd4) & He).
    assert (E3: D3 = D') by (unfold D3, D2, D1, D', hcf5_p6_setc, dev_set_cc; simpl; rewrite Hb; reflexivity).
    rewrite E3. rewrite <- hcf5_p6_ds_W.
    gather_SEP (hbytes Ews r _) (hcf5_p6_srest _ _).
    replace_SEP 0 (shim_core gv (shim_draw S r)).
    { rewrite hcf5_p6_core_open, (hcf5_p6_log S r Hlr). entailer!. }
    assert (Hinv': hcf5_inv R L (shim_draw S r) w D' P T KE true)
      by exact (conj Ha (conj Hb (conj Hc (conj (conj Hd1 (conj eq_refl (conj Hd3 Hd4))) He)))).
    assert (Hsame': hcf5_same L D' P T KE (shim_draw S r) w D' sn0 P0 r0 S0 w0 h0)
      by exact (conj (hcf5_dev_eqb_refl _ _) (conj Hsn (conj Hpr (conj Hr (conj Hsh (conj Hke Hh0)))))).
    assert (HPx': hcf5_Px1 x25519 D' RAW /\ hcf5_qok L H) by exact (conj HPx HQ).
    Exists R (shim_draw S r) w D' P T KE.
    Exists D' sn0 P0 r0. Exists S0 w0 h0 RAW H.
    unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars, hcf5_X5, shim_state4. cbn [app].
    entailer!.
Qed.

End P6.
