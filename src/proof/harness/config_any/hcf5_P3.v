(* law config_any: main's phase P3, statements 36..37: step 3: wg_cookie_checker_precompute_device_keys(&w.cookie_checker), the edits of ds (m_label_key or bytes_set).
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

#[local] Instance hcf5_p3_cceH : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.
#[local] Instance hcf5_p3_cceK : change_composite_env CKS W_config_any.
Proof. make_cs_preserve CKS W_config_any. Defined.

Lemma hcf5_p3_hb_W sh bs p : hbytes sh bs p = @data_at W_config_any sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof.
  unfold hbytes. apply equal_f.
  apply (@data_at_change_composite HCS W_config_any _ sh (tarray tuchar (Zlength bs))); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p3_ds_W sh v p : @data_at CKS sh t_devsnap v p = @data_at W_config_any sh t_devsnap v p.
Proof.
  apply equal_f.
  apply (@data_at_change_composite CKS W_config_any _ sh t_devsnap); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* a Tsh byte buffer as an Ers part (to share one share with a constant) and the rest *)
Lemma hcf5_p3_ers_split bs p : hbytes Tsh bs p = (hbytes Ers bs p * hbytes (Share.comp Ers) bs p)%logic.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

(* the m_identity struct, field by field (at the world) *)
Lemma hcf5_p3_mid_open sh M id : Zlength (mi_priv M) = 32 -> Zlength (mi_pub M) = 32 ->
  @data_at HCS sh t_mident (mident_val M) id =
  (!! @field_compatible W_config_any t_mident [] id &&
   (hbytes sh (mi_priv M) (@field_address W_config_any t_mident (DOT HF._priv) id) *
    hbytes sh (mi_pub M) (@field_address W_config_any t_mident (DOT HF._pub) id) *
    @field_at W_config_any sh t_mident (DOT HF._ok) (Vint (if mi_ok M then Int.one else Int.zero)) id))%logic.
Proof.
  intros L1 L2.
  rewrite (@data_at_change_composite HCS W_config_any _ sh t_mident (mident_val M) (mident_val M) (JMeq_refl _))
    by prove_cs_preserve_type.
  rewrite !hcf5_p3_hb_W, L1, L2.
  apply pred_ext; [assert_PROP (@field_compatible W_config_any t_mident [] id) by entailer! | Intros];
  unfold_data_at (data_at _ _ _ id);
  rewrite !(@field_at_data_at W_config_any sh t_mident (DOT _));
  unfold mident_val; simpl; entailer!.
Qed.

Definition hcf5_p3_setk (D: device) (ek mk: list byte) : device :=
  dev_set_cc D (mkChk (cc_secret (d_cc D)) ek mk (cc_birth (d_cc D)) (cc_dev (d_cc D))).

(* the dev_snap's two checker-key fields, one at a time (ramification at the world) *)
Lemma hcf5_p3_dek sh D h p s :
  @data_at W_config_any sh t_devsnap (devsnap_val D h) p |-- (
  @data_at_ W_config_any sh (tarray tuchar 32) (@field_address W_config_any t_devsnap (DOT HF._cookie_encryption_key) p) *
  (@data_at W_config_any sh (tarray tuchar 32) (bytes s) (@field_address W_config_any t_devsnap (DOT HF._cookie_encryption_key) p) -*
   @data_at W_config_any sh t_devsnap (devsnap_val (hcf5_p3_setk D s (cc_mkey (d_cc D))) h) p))%logic.
Proof.
  assert_PROP (@field_compatible W_config_any t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HF._cookie_encryption_key)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - rewrite field_at_data_at. apply sepcon_derives; [apply data_at_data_at_ |].
    apply (allp_left _ (bytes s)). apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hcf5_p3_dmk sh D h p s :
  @data_at W_config_any sh t_devsnap (devsnap_val D h) p |-- (
  @data_at_ W_config_any sh (tarray tuchar 32) (@field_address W_config_any t_devsnap (DOT HF._message_mac1_key) p) *
  (@data_at W_config_any sh (tarray tuchar 32) (bytes s) (@field_address W_config_any t_devsnap (DOT HF._message_mac1_key) p) -*
   @data_at W_config_any sh t_devsnap (devsnap_val (hcf5_p3_setk D (cc_ekey (d_cc D)) s) h) p))%logic.
Proof.
  assert_PROP (@field_compatible W_config_any t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HF._message_mac1_key)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - rewrite field_at_data_at. apply sepcon_derives; [apply data_at_data_at_ |].
    apply (allp_left _ (bytes s)). apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hcf5_p3_setk2 D a b c d : hcf5_p3_setk (hcf5_p3_setk D a b) c d = hcf5_p3_setk D c d.
Proof. reflexivity. Qed.

Lemma hcf5_p3_label_len l p : Zlength (label_key l p) = 32.
Proof.
  unfold label_key, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
    WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma hcf5_p3_mp sh k p (Q: mpred) : Zlength k = 32 ->
  (hbytes sh k p * (@data_at W_config_any sh (tarray tuchar 32) (bytes k) p -* Q) |-- Q)%logic.
Proof. intros Hl. rewrite hcf5_p3_hb_W, Hl. apply wand_frame_elim. Qed.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_p3_keys ID0 RAW :
  checker_keys (identity_of x25519 ID0 RAW) =
  if mi_ok (mident_of x25519 RAW)
  then (label_key cookie_label (mi_pub (mident_of x25519 RAW)), label_key mac1_label (mi_pub (mident_of x25519 RAW)))
  else (zeros32, zeros32).
Proof.
  unfold checker_keys, identity_of, mident_of; simpl.
  destruct (memneq_bool RAW zeros32); simpl; reflexivity.
Qed.

Lemma hcf5_p3_dev D ID0 RAW : d_id D = identity_of x25519 ID0 RAW ->
  dev_set_cc D (checker_set_keys (d_cc D) (checker_keys (d_id D))) =
  hcf5_p3_setk D (fst (checker_keys (d_id D))) (snd (checker_keys (d_id D))).
Proof. reflexivity. Qed.
End Pure.

Section P3.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_P3_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) hcf5_P3
    (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HX. unfold hcf5_SX1, hcf5_Delta, hcf5_R, hcf5_P3. simplify_func_tycontext. abbreviate_semax.
  unfold hcf5_F, hcf5_Fx.
  Intros R S w D P T KE D0. Intros sn0 P0 r0 S0 w0 h0 RAW.
  destruct H as [HRAW [ID0 [HID0 HDID]]].
  destruct H0 as (Hrun & Hboot & Hw & Hdok & Hpok & Hslots & HTok & Hks).
  pose proof H1 as Hsame. destruct H1 as (Hdev & _).
  apply hcf5_dev_eqb_eq in Hdev. destruct Hdev as [-> _].
  unfold hcf5_core, hcf5_globs, hcf5_X1. cbn [app].
  assert (Hcc: cc_dev (d_cc D) = l_w L) by apply Hdok.
  assert_PROP (isptr (l_w L)) as Pw by (go_lowerx; apply prop_right;
    match goal with K: lvar_denote HF._w _ _ _ |- _ => eapply (lvar_isptr HF._w); exact K end).
  forward_call (gv, Tsh, l_w L, D).
  { go_lowerx. apply prop_right. destruct (l_w L); try contradiction; reflexivity. }
  assert (Lpriv: Zlength (mi_priv (mident_of x25519 RAW)) = 32) by (simpl; unfold clamp; list_solve).
  assert (Lpub: Zlength (mi_pub (mident_of x25519 RAW)) = 32) by (simpl; apply HX).
  rewrite (hcf5_p3_mid_open Tsh _ (l_id L) Lpriv Lpub).
  repeat flatten_sepcon_in_SEP. Intros.
  forward.
  set (MI := mident_of x25519 RAW) in *.
  assert (Hk: checker_keys (d_id D) =
              if mi_ok MI then (label_key cookie_label (mi_pub MI), label_key mac1_label (mi_pub MI))
              else (zeros32, zeros32)) by (rewrite HDID; apply hcf5_p3_keys).
  rewrite hcf5_p3_ds_W.
  unfold wg_consts, hcf5_consts. Intros.
  set (D' := dev_set_cc D (checker_set_keys (d_cc D) (checker_keys (d_id D)))).
  assert (Px: hcf5_Px1 x25519 D' RAW) by (split; [exact HRAW | exists ID0; split; [exact HID0 | exact HDID]]).
  assert (Inv: hcf5_inv R L S w D' P T KE false)
    by (unfold hcf5_inv, hcf5_dok in *; simpl; tauto).
  assert (Same: hcf5_same L D' P T KE S w D' sn0 P0 r0 S0 w0 h0)
    by (destruct Hsame as (_ & Hs); split; [apply hcf5_dev_eqb_refl | exact Hs]).
  destruct (mi_ok MI) eqn:Hok.
  - (* id.ok: the two label keys *)
    forward_if; [| discriminate].
    rewrite (hcf5_p3_ers_split (mi_pub MI)).
    change (hc_const gv HF._x_config_any__M_LABEL_COOKIE cookie_label)
      with (hbytes Ers cookie_label (gv HF._x_config_any__M_LABEL_COOKIE)).
    change (hc_const gv HF._x_config_any__M_LABEL_MAC1 mac1_label)
      with (hbytes Ers mac1_label (gv HF._x_config_any__M_LABEL_MAC1)).
    sep_apply (hcf5_p3_dek Tsh D (l_p L) (l_ds L) (label_key cookie_label (mi_pub MI))).
    rewrite <- hcf5_conv_bytes.
    forward_call (gv, Tsh, @field_address W_config_any t_devsnap (DOT HF._cookie_encryption_key) (l_ds L),
                  Ers, gv HF._x_config_any__M_LABEL_COOKIE, cookie_label,
                  @field_address W_config_any t_mident (DOT HF._pub) (l_id L), mi_pub MI).
    { cancel. }
    sep_apply (hcf5_p3_mp Tsh (label_key cookie_label (mi_pub MI))
                 (@field_address W_config_any t_devsnap (DOT HF._cookie_encryption_key) (l_ds L))
                 (@data_at W_config_any Tsh t_devsnap (devsnap_val (hcf5_p3_setk D (label_key cookie_label (mi_pub MI))
                    (cc_mkey (d_cc D))) (l_p L)) (l_ds L))
                 (hcf5_p3_label_len _ _)).
    sep_apply (hcf5_p3_dmk Tsh (hcf5_p3_setk D (label_key cookie_label (mi_pub MI)) (cc_mkey (d_cc D)))
                 (l_p L) (l_ds L) (label_key mac1_label (mi_pub MI))).
    rewrite <- hcf5_conv_bytes.
    forward_call (gv, Tsh, @field_address W_config_any t_devsnap (DOT HF._message_mac1_key) (l_ds L),
                  Ers, gv HF._x_config_any__M_LABEL_MAC1, mac1_label,
                  @field_address W_config_any t_mident (DOT HF._pub) (l_id L), mi_pub MI).
    { cancel. }
    sep_apply (hcf5_p3_mp Tsh (label_key mac1_label (mi_pub MI))
                 (@field_address W_config_any t_devsnap (DOT HF._message_mac1_key) (l_ds L))
                 (@data_at W_config_any Tsh t_devsnap (devsnap_val (hcf5_p3_setk
                    (hcf5_p3_setk D (label_key cookie_label (mi_pub MI)) (cc_mkey (d_cc D)))
                    (cc_ekey (d_cc (hcf5_p3_setk D (label_key cookie_label (mi_pub MI)) (cc_mkey (d_cc D)))))
                    (label_key mac1_label (mi_pub MI))) (l_p L)) (l_ds L))
                 (hcf5_p3_label_len _ _)).
    sep_apply (derives_refl' _ _ (eq_sym (hcf5_p3_ers_split (mi_pub MI)
                 (@field_address W_config_any t_mident (DOT HF._pub) (l_id L))))).
    assert (HD': hcf5_p3_setk
                   (hcf5_p3_setk D (label_key cookie_label (mi_pub MI)) (cc_mkey (d_cc D)))
                   (cc_ekey (d_cc (hcf5_p3_setk D (label_key cookie_label (mi_pub MI)) (cc_mkey (d_cc D)))))
                   (label_key mac1_label (mi_pub MI)) = D')
      by (unfold D', checker_set_keys; rewrite Hk; reflexivity).
    rewrite HD'.
    Exists R S w D' P T KE D'. Exists sn0 P0 r0 S0 w0 h0 RAW.
    unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_X1, hcf5_lvars, wg_consts, hcf5_consts. cbn [app].
    fold MI. rewrite (hcf5_p3_mid_open Tsh _ (l_id L) Lpriv Lpub). rewrite Hok.
    rewrite hcf5_p3_ds_W.
    change (hc_const gv HF._x_config_any__M_LABEL_COOKIE cookie_label)
      with (hbytes Ers cookie_label (gv HF._x_config_any__M_LABEL_COOKIE)).
    change (hc_const gv HF._x_config_any__M_LABEL_MAC1 mac1_label)
      with (hbytes Ers mac1_label (gv HF._x_config_any__M_LABEL_MAC1)).
    entailer!.
  - forward_if; [exfalso; auto |].
    sep_apply (hcf5_p3_dek Tsh D (l_p L) (l_ds L) zeros32).
    rewrite <- hcf5_conv_bytes.
    forward_call (Tsh, @field_address W_config_any t_devsnap (DOT HF._cookie_encryption_key) (l_ds L), Byte.zero, 32).
    { cancel. }
    change (Zrepeat Byte.zero 32) with zeros32.
    sep_apply (hcf5_p3_mp Tsh zeros32
                 (@field_address W_config_any t_devsnap (DOT HF._cookie_encryption_key) (l_ds L))
                 (@data_at W_config_any Tsh t_devsnap (devsnap_val (hcf5_p3_setk D zeros32 (cc_mkey (d_cc D))) (l_p L)) (l_ds L))
                 eq_refl).
    sep_apply (hcf5_p3_dmk Tsh (hcf5_p3_setk D zeros32 (cc_mkey (d_cc D))) (l_p L) (l_ds L) zeros32).
    rewrite <- hcf5_conv_bytes.
    forward_call (Tsh, @field_address W_config_any t_devsnap (DOT HF._message_mac1_key) (l_ds L), Byte.zero, 32).
    { cancel. }
    change (Zrepeat Byte.zero 32) with zeros32.
    sep_apply (hcf5_p3_mp Tsh zeros32
                 (@field_address W_config_any t_devsnap (DOT HF._message_mac1_key) (l_ds L))
                 (@data_at W_config_any Tsh t_devsnap (devsnap_val (hcf5_p3_setk
                    (hcf5_p3_setk D zeros32 (cc_mkey (d_cc D)))
                    (cc_ekey (d_cc (hcf5_p3_setk D zeros32 (cc_mkey (d_cc D))))) zeros32) (l_p L)) (l_ds L))
                 eq_refl).
    assert (HD': hcf5_p3_setk
                   (hcf5_p3_setk D zeros32 (cc_mkey (d_cc D)))
                   (cc_ekey (d_cc (hcf5_p3_setk D zeros32 (cc_mkey (d_cc D))))) zeros32 = D')
      by (unfold D', checker_set_keys; rewrite Hk; reflexivity).
    rewrite HD'.
    Exists R S w D' P T KE D'. Exists sn0 P0 r0 S0 w0 h0 RAW.
    unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_X1, hcf5_lvars, wg_consts, hcf5_consts. cbn [app].
    fold MI. rewrite (hcf5_p3_mid_open Tsh _ (l_id L) Lpriv Lpub). rewrite Hok.
    rewrite hcf5_p3_ds_W.
    entailer!.
Qed.

End P3.
