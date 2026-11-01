(* law config_any: main's phase P1, statements 25..30: step 1: nondet_bytes(raw), m_identity_of(&id, raw), wg_noise_set_static_identity_private_key(&w.static_identity, raw), the edits of ds.
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

#[local] Instance hcf5_p1_cceN : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.
#[local] Instance hcf5_p1_cceH : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.
#[local] Instance hcf5_p1_cceK : change_composite_env CKS W_config_any.
Proof. make_cs_preserve CKS W_config_any. Defined.

(* nondet_bytes's result as hbytes *)
Lemma hcf5_p1_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_config_any sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros Hn Hb. subst n. unfold hbytes, bytes. rewrite Zlength_map.
  rewrite (@data_at_change_composite HCS W_config_any _ sh (tarray tuchar (Zlength bs))
             (map Vubyte (map Byte.repr bs)) (map Vubyte (map Byte.repr bs)) (JMeq_refl _))
    by prove_cs_preserve_type.
  f_equal. rewrite map_map. induction Hb; simpl; [reflexivity |]. f_equal; [| assumption].
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia). reflexivity.
Qed.

Lemma hcf5_p1_hb_W sh bs p : hbytes sh bs p = @data_at W_config_any sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof.
  unfold hbytes. apply equal_f.
  apply (@data_at_change_composite HCS W_config_any _ sh (tarray tuchar (Zlength bs))); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p1_ba_W sh bs p : bytes_at sh bs p = @data_at W_config_any sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof.
  unfold bytes_at. apply equal_f.
  apply (@data_at_change_composite Noise.CS W_config_any _ sh (tarray tuchar (Zlength bs))); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p1_hb_ba sh bs p : hbytes sh bs p = bytes_at sh bs p.
Proof. rewrite hcf5_p1_hb_W, hcf5_p1_ba_W. reflexivity. Qed.

Lemma hcf5_p1_ds_W sh v p : @data_at CKS sh t_devsnap v p = @data_at W_config_any sh t_devsnap v p.
Proof.
  apply equal_f.
  apply (@data_at_change_composite CKS W_config_any _ sh t_devsnap); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the device without its identity *)
Definition hcf5_p1_drest (sh: share) (wg: val) (D: device) : mpred :=
  (@field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg *
   checker_rep sh (cc_addr wg) (d_cc D) *
   @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   @field_at Noise.CS sh t_dev [StructField I._index_hashtable] (d_itab D) wg)%logic.

Lemma hcf5_p1_dev_open sh wg D :
  device_rep sh wg D =
  (!! @field_compatible Noise.CS t_dev [] wg && (identity_rep sh (id_addr wg) (d_id D) * hcf5_p1_drest sh wg D))%logic.
Proof. unfold device_rep, hcf5_p1_drest. apply pred_ext; entailer!. Qed.

Lemma hcf5_p1_dev_close sh wg D ID :
  (!! @field_compatible Noise.CS t_dev [] wg && (identity_rep sh (id_addr wg) ID * hcf5_p1_drest sh wg D))%logic
  |-- device_rep sh wg (dev_set_id D ID).
Proof. rewrite hcf5_p1_dev_open. apply derives_refl. Qed.

(* the m_identity struct, field by field (at the world) *)
Lemma hcf5_p1_mid_open sh M id : Zlength (mi_priv M) = 32 -> Zlength (mi_pub M) = 32 ->
  @data_at HCS sh t_mident (mident_val M) id =
  (!! @field_compatible W_config_any t_mident [] id &&
   (hbytes sh (mi_priv M) (@field_address W_config_any t_mident (DOT HF._priv) id) *
    hbytes sh (mi_pub M) (@field_address W_config_any t_mident (DOT HF._pub) id) *
    @field_at W_config_any sh t_mident (DOT HF._ok) (Vint (if mi_ok M then Int.one else Int.zero)) id))%logic.
Proof.
  intros L1 L2.
  rewrite (@data_at_change_composite HCS W_config_any _ sh t_mident (mident_val M) (mident_val M) (JMeq_refl _))
    by prove_cs_preserve_type.
  rewrite !hcf5_p1_hb_W, L1, L2.
  apply pred_ext; [assert_PROP (@field_compatible W_config_any t_mident [] id) by entailer! | Intros];
  unfold_data_at (data_at _ _ _ id);
  rewrite !(@field_at_data_at W_config_any sh t_mident (DOT _));
  unfold mident_val; simpl; entailer!.
Qed.

(* the dev_snap's identity fields, one at a time (ramification at the world) *)
Lemma hcf5_p1_dpriv sh D h p s :
  @data_at W_config_any sh t_devsnap (devsnap_val D h) p |--
  @data_at_ W_config_any sh (tarray tuchar 32) (@field_address W_config_any t_devsnap (DOT HF._static_private) p) *
  (@data_at W_config_any sh (tarray tuchar 32) (bytes s) (@field_address W_config_any t_devsnap (DOT HF._static_private) p) -*
   @data_at W_config_any sh t_devsnap (devsnap_val (dev_set_id D (mkId (id_pub (d_id D)) s (id_has (d_id D)))) h) p).
Proof.
  assert_PROP (@field_compatible W_config_any t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HF._static_private)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - rewrite field_at_data_at. apply sepcon_derives; [apply data_at_data_at_ |].
    apply (allp_left _ (bytes s)). apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hcf5_p1_dpub sh D h p s :
  @data_at W_config_any sh t_devsnap (devsnap_val D h) p |--
  @data_at_ W_config_any sh (tarray tuchar 32) (@field_address W_config_any t_devsnap (DOT HF._static_public) p) *
  (@data_at W_config_any sh (tarray tuchar 32) (bytes s) (@field_address W_config_any t_devsnap (DOT HF._static_public) p) -*
   @data_at W_config_any sh t_devsnap (devsnap_val (dev_set_id D (mkId s (id_priv (d_id D)) (id_has (d_id D)))) h) p).
Proof.
  assert_PROP (@field_compatible W_config_any t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HF._static_public)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - rewrite field_at_data_at. apply sepcon_derives; [apply data_at_data_at_ |].
    apply (allp_left _ (bytes s)). apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hcf5_p1_dhas sh D h p b :
  @data_at W_config_any sh t_devsnap (devsnap_val D h) p |--
  @field_at_ W_config_any sh t_devsnap (DOT HF._has_identity) p *
  (@field_at W_config_any sh t_devsnap (DOT HF._has_identity) (Val.of_bool b) p -*
   @data_at W_config_any sh t_devsnap (devsnap_val (dev_set_id D (mkId (id_pub (d_id D)) (id_priv (d_id D)) b)) h) p).
Proof.
  assert_PROP (@field_compatible W_config_any t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HF._has_identity)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - apply sepcon_derives; [apply field_at_field_at_ |].
    apply (allp_left _ (Val.of_bool b)). apply wand_derives; [apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hcf5_p1_iszero RAW : Zlength RAW = 32 -> is_zero RAW = negb (memneq_bool RAW zeros32).
Proof.
  intros HL. unfold is_zero, bytes_eqb, memneq_bool, zeros, zeros32. rewrite HL.
  destruct (list_eq_dec Byte.eq_dec RAW (Zrepeat Byte.zero 32)); reflexivity.
Qed.

Lemma hcf5_p1_clamp_len s : Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros HL. unfold clamp. rewrite !upd_Znth_Zlength; rewrite ?upd_Znth_Zlength; lia. Qed.

Lemma hcf5_p1_hout_len sh n p (A: list byte) : Zlength A = n -> hout sh n p = hout sh (Zlength A) p.
Proof. intros ->. reflexivity. Qed.

Lemma hcf5_p1_hb_W32 sh bs p : Zlength bs = 32 ->
  hbytes sh bs p = @data_at W_config_any sh (tarray tuchar 32) (bytes bs) p.
Proof. intros HL. rewrite hcf5_p1_hb_W, HL. reflexivity. Qed.

Lemma hcf5_p1_bval (b: bool) :
  Vint (if Int.eq (if b then Int.one else Int.zero) Int.zero then Int.zero else Int.one) = Val.of_bool b.
Proof. destruct b; reflexivity. Qed.

Section P1.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_P1_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_SX0 gv L FR) hcf5_P1
    (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HH. unfold hcf5_SX0, hcf5_SX1, hcf5_Delta, hcf5_R, hcf5_P1. simplify_func_tycontext. abbreviate_semax.
  Intros R S w D P T KE. Intros D0 sn0 P0 r0 S0 w0 h0.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars, hcf5_X0. cbn [app].
  Intros.
  destruct H0 as (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh0).
  apply hcf5_dev_eqb_eq in Hdev. destruct Hdev as [-> _].
  (* nondet_bytes(raw, 32) *)
  rewrite (hcf5_conv_bytes Tsh 32 (l_raw L)).
  forward_call (l_raw L, 32, Tsh). Intros bs.
  rewrite (hcf5_p1_nd Tsh 32 bs) by tauto.
  set (RAW := map Byte.repr bs).
  assert (HL: Zlength RAW = 32) by (unfold RAW; rewrite Zlength_map; tauto).
  (* m_identity_of(&id, raw) *)
  unfold hcf5_consts. Intros.
  forward_call (gv, Tsh, l_id L, Tsh, l_raw L, RAW).
  (* wg_noise_set_static_identity_private_key(&w.static_identity, raw) *)
  rewrite hcf5_p1_dev_open. Intros.
  rewrite (hcf5_p1_hb_ba Tsh RAW (l_raw L)).
  assert_PROP (id_ok (d_id D)) as Hido by (unfold identity_rep; entailer!).
  forward_call (gv, Tsh, id_addr (l_w L), d_id D, Tsh, l_raw L, RAW).
  rewrite <- (hcf5_p1_hb_ba Tsh RAW (l_raw L)).
  set (D' := dev_set_id D (identity_of x25519 (d_id D) RAW)).
  gather_SEP (identity_rep _ _ _) (hcf5_p1_drest _ _ _).
  replace_SEP 0 (device_rep Tsh (l_w L) D').
  { unfold D'. rewrite hcf5_p1_dev_open. entailer!. apply derives_refl. }
  (* bytes_copy(ds.static_private, id.priv, 32) *)
  assert (Hlc: Zlength (clamp RAW) = 32) by (apply hcf5_p1_clamp_len; exact HL).
  assert (Hlp: Zlength (x25519 RAW basepoint9) = 32) by apply HH.
  rewrite hcf5_p1_ds_W.
  assert_PROP (field_compatible t_devsnap [] (l_ds L)) as Hfds by entailer!.
  sep_apply (hcf5_p1_dpriv Tsh D (l_p L) (l_ds L) (clamp RAW)).
  rewrite (hcf5_p1_mid_open Tsh (mident_of x25519 RAW)) by assumption. Intros.
  simpl mi_priv. simpl mi_pub. simpl mi_ok.
  rewrite <- (hcf5_conv_bytes Tsh 32 (field_address t_devsnap (DOT HF._static_private) (l_ds L))).
  rewrite (hcf5_p1_hout_len Tsh 32 _ (clamp RAW) Hlc).
  forward_call (Tsh, field_address t_devsnap (DOT HF._static_private) (l_ds L), Tsh,
                field_address t_mident (DOT HF._priv) (l_id L), clamp RAW).
  { rewrite Hlc. entailer!. simpl. rewrite !field_address_offset by auto with field_compatible. reflexivity. }
  rewrite (hcf5_p1_hb_W32 Tsh (clamp RAW) (field_address t_devsnap (DOT HF._static_private) (l_ds L)) Hlc).
  set (D1 := dev_set_id D (mkId (id_pub (d_id D)) (clamp RAW) (id_has (d_id D)))).
  sep_apply (wand_frame_elim (@data_at W_config_any Tsh (tarray tuchar 32) (bytes (clamp RAW))
               (field_address t_devsnap (DOT HF._static_private) (l_ds L)))
               (@data_at W_config_any Tsh t_devsnap (devsnap_val D1 (l_p L)) (l_ds L))).
  (* t'5 = bytes_zero(raw, 32) *)
  forward_call (Tsh, l_raw L, RAW).
  { rewrite HL. entailer!. }
  set (D2 := dev_set_id D (mkId (if memneq_bool RAW zeros32 then x25519 RAW basepoint9 else id_pub (d_id D))
                                (clamp RAW) (id_has (d_id D)))).
  match goal with |- semax _ (PROPx ?Pp (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    let Rs' := constr:(replace_nth 1 Rs (@data_at W_config_any Tsh t_devsnap (devsnap_val D2 (l_p L)) (l_ds L))) in
    let Rs'' := eval cbv beta iota delta [replace_nth] in Rs' in
    forward_if (PROPx Pp (LOCALx Q (SEPx Rs'')))
  end.
  - assert (Hm: memneq_bool RAW zeros32 = true).
    { rewrite hcf5_p1_iszero in H4 by exact HL.
      destruct (memneq_bool RAW zeros32); [reflexivity | exfalso; apply Int.one_not_zero; exact H4]. }
    assert (E2: dev_set_id D1 (mkId (x25519 RAW basepoint9) (id_priv (d_id D1)) (id_has (d_id D1))) = D2)
      by (unfold D2, D1; rewrite Hm; reflexivity).
    sep_apply (hcf5_p1_dpub Tsh D1 (l_p L) (l_ds L) (x25519 RAW basepoint9)).
    rewrite E2.
    rewrite <- (hcf5_conv_bytes Tsh 32 (field_address t_devsnap (DOT HF._static_public) (l_ds L))).
    rewrite (hcf5_p1_hout_len Tsh 32 _ (x25519 RAW basepoint9) Hlp).
    forward_call (Tsh, field_address t_devsnap (DOT HF._static_public) (l_ds L), Tsh,
                  field_address t_mident (DOT HF._pub) (l_id L), x25519 RAW basepoint9).
    { rewrite Hlp. entailer!. simpl. rewrite !field_address_offset by auto with field_compatible. reflexivity. }
    { cancel. }
    rewrite (hcf5_p1_hb_W32 Tsh (x25519 RAW basepoint9) (field_address t_devsnap (DOT HF._static_public) (l_ds L)) Hlp).
    sep_apply (wand_frame_elim (@data_at W_config_any Tsh (tarray tuchar 32) (bytes (x25519 RAW basepoint9))
                 (field_address t_devsnap (DOT HF._static_public) (l_ds L)))
                 (@data_at W_config_any Tsh t_devsnap (devsnap_val D2 (l_p L)) (l_ds L))).
    entailer!.
  - assert (Hm: memneq_bool RAW zeros32 = false).
    { rewrite hcf5_p1_iszero in H4 by exact HL.
      destruct (memneq_bool RAW zeros32); [exfalso; apply H4; reflexivity | reflexivity]. }
    assert (E2: D1 = D2) by (unfold D2, D1; rewrite Hm; reflexivity).
    forward. rewrite E2. entailer!.
  - forward.
    sep_apply (hcf5_p1_dhas Tsh D2 (l_p L) (l_ds L)
                 (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)).
    Intros.
    forward.
    rewrite hcf5_p1_bval.
    assert (E3: dev_set_id D2 (mkId (id_pub (d_id D2)) (id_priv (d_id D2))
                  (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)) = D') by reflexivity.
    rewrite E3.
    sep_apply (wand_frame_elim
      (@field_at W_config_any Tsh t_devsnap (DOT HF._has_identity)
         (Val.of_bool (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)) (l_ds L))
      (@data_at W_config_any Tsh t_devsnap (devsnap_val D' (l_p L)) (l_ds L))).
    rewrite <- hcf5_p1_ds_W.
    gather_SEP (hbytes Tsh (clamp RAW) _) (hbytes Tsh (x25519 RAW basepoint9) _) (field_at Tsh t_mident _ _ (l_id L)).
    replace_SEP 0 (@data_at HCS Tsh t_mident (mident_val (mident_of x25519 RAW)) (l_id L)).
    { rewrite (hcf5_p1_mid_open Tsh (mident_of x25519 RAW)) by assumption. entailer!. }
    assert (Hinv: hcf5_inv R L S w D' P T KE false) by exact H.
    assert (Hsame: hcf5_same L D' P T KE S w D' sn0 P0 r0 S0 w0 h0)
      by exact (conj (hcf5_dev_eqb_refl _ _) (conj Hsn (conj Hpr (conj Hr (conj Hsh (conj Hke Hh0)))))).
    assert (HPx: hcf5_Px1 x25519 D' RAW) by (split; [exact HL | exists (d_id D); split; [exact Hido | reflexivity]]).
    Exists R S w D' P T KE.
    Exists D' sn0 P0 r0 S0 w0 h0 RAW.
    unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars, hcf5_X1, hcf5_consts. cbn [app].
    entailer!.
Qed.

End P1.
