(* law config_any: main's phase P4, statements 39..41: step 4: wg_cookie_checker_precompute_peer_keys(&p), m_label_key into ps0.cookie's two keys.
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

Section NoiseCS4.
#[local] Existing Instance Noise.CS.

(* the peer without its handshake and its cookie *)
Definition hcf5_p4_prest (sh: share) (p: val) (P: peer) : mpred :=
  (!! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p))%logic.

Lemma hcf5_p4_peer_split sh p P :
  peer_rep sh p P =
  (hs_rep sh (hs_addr p) (p_hs P) * cookie_rep sh (cookie_addr p) (p_cookie P) * hcf5_p4_prest sh p P)%logic.
Proof.
  unfold peer_rep, hcf5_p4_prest. rewrite sepcon_andp_prop.
  f_equal. apply pred_ext; cancel.
Qed.

Lemma hcf5_p4_peer_join sh p P C :
  (hs_rep sh (hs_addr p) (p_hs P) * cookie_rep sh (cookie_addr p) C * hcf5_p4_prest sh p P)%logic =
  peer_rep sh p (p_set_cookie P C).
Proof. rewrite hcf5_p4_peer_split. destruct P; reflexivity. Qed.

Lemma hcf5_p4_peer_join' sh p P C :
  (hs_rep sh (hs_addr p) (p_hs P) * cookie_rep sh (cookie_addr p) C * hcf5_p4_prest sh p P)%logic |--
  peer_rep sh p (p_set_cookie P C).
Proof. rewrite hcf5_p4_peer_join. apply derives_refl. Qed.

Lemma hcf5_p4_fc sh p P : peer_rep sh p P |-- !! field_compatible t_peer [] p.
Proof. unfold peer_rep. entailer!. Qed.
End NoiseCS4.

(* the peer with its cookie's decryption / mac1 key replaced *)
Definition hcf5_p4_setd (P: peer) (k: list byte) : peer :=
  let C := p_cookie P in
  p_set_cookie P (mkCookie (ck_birth C) (ck_valid C) (ck_cookie C) (ck_sent C) (ck_last_mac1 C) k (ck_mkey C)).
Definition hcf5_p4_setm (P: peer) (k: list byte) : peer :=
  let C := p_cookie P in
  p_set_cookie P (mkCookie (ck_birth C) (ck_valid C) (ck_cookie C) (ck_sent C) (ck_last_mac1 C) (ck_dkey C) k).

Definition hcf5_p4_dk (p: val) : val :=
  @field_address CKS t_prsnap [StructField HF._cookie_decryption_key; StructField HF._cookie] p.
Definition hcf5_p4_mk (p: val) : val :=
  @field_address CKS t_prsnap [StructField HF._message_mac1_key; StructField HF._cookie] p.

#[local] Instance hcf5_p4_cceHK : change_composite_env HCS CKS.
Proof. make_cs_preserve HCS CKS. Defined.

Lemma hcf5_p4_hb32 sh s p :
  @data_at HCS sh (tarray tuchar 32) (bytes s) p = @data_at CKS sh (tarray tuchar 32) (bytes s) p.
Proof.
  apply equal_f.
  apply (@data_at_change_composite HCS CKS _ sh (tarray tuchar 32)); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p4_ho32 sh p :
  @data_at_ HCS sh (tarray tuchar 32) p = @data_at_ CKS sh (tarray tuchar 32) p.
Proof.
  unfold data_at_, field_at_. apply equal_f.
  apply (@data_at_change_composite HCS CKS _ sh (tarray tuchar 32)); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p4_psd sh P p s :
  @data_at CKS sh t_prsnap (prsnap_val P) p |--
  (@data_at_ HCS sh (tarray tuchar 32) (hcf5_p4_dk p) *
   (@data_at HCS sh (tarray tuchar 32) (bytes s) (hcf5_p4_dk p) -*
    @data_at CKS sh t_prsnap (prsnap_val (hcf5_p4_setd P s)) p))%logic.
Proof.
  rewrite hcf5_p4_ho32, hcf5_p4_hb32.
  assert_PROP (@field_compatible CKS t_prsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (nested_field_ramif sh t_prsnap [] [StructField HF._cookie_decryption_key; StructField HF._cookie]) |].
  - apply JMeq_refl.
  - simpl app; auto with field_compatible.
  - simpl app. apply sepcon_derives.
    + rewrite field_at_data_at. apply data_at_data_at_.
    + apply (allp_left _ (bytes s)). apply (allp_left _ (bytes s)). rewrite prop_imp by apply JMeq_refl.
      apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
      unfold data_at. apply derives_refl.
Qed.

Lemma hcf5_p4_psm sh P p s :
  @data_at CKS sh t_prsnap (prsnap_val P) p |--
  (@data_at_ HCS sh (tarray tuchar 32) (hcf5_p4_mk p) *
   (@data_at HCS sh (tarray tuchar 32) (bytes s) (hcf5_p4_mk p) -*
    @data_at CKS sh t_prsnap (prsnap_val (hcf5_p4_setm P s)) p))%logic.
Proof.
  rewrite hcf5_p4_ho32, hcf5_p4_hb32.
  assert_PROP (@field_compatible CKS t_prsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (nested_field_ramif sh t_prsnap [] [StructField HF._message_mac1_key; StructField HF._cookie]) |].
  - apply JMeq_refl.
  - simpl app; auto with field_compatible.
  - simpl app. apply sepcon_derives.
    + rewrite field_at_data_at. apply data_at_data_at_.
    + apply (allp_left _ (bytes s)). apply (allp_left _ (bytes s)). rewrite prop_imp by apply JMeq_refl.
      apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
      unfold data_at. apply derives_refl.
Qed.

(* a Tsh byte buffer as an Ers part (to share one share with a constant) and the rest *)
Lemma hcf5_p4_ers_split bs p : hbytes Tsh bs p = (hbytes Ers bs p * hbytes (Share.comp Ers) bs p)%logic.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

Lemma hcf5_p4_label_len l p : Zlength (label_key l p) = 32.
Proof.
  unfold label_key, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
    WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma hcf5_p4_mp (A B: mpred) : (A * (A -* B))%logic |-- B.
Proof. apply modus_ponens_wand. Qed.

Lemma hcf5_p4_inv R L S w D P T KE qin C :
  hcf5_inv R L S w D P T KE qin -> hcf5_inv R L S w D (p_set_cookie P C) T KE qin.
Proof.
  unfold hcf5_inv, hcf5_pok, hcf5_slots_ok. destruct P; simpl. tauto.
Qed.

Lemma hcf5_p4_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 C :
  hcf5_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 ->
  hcf5_same L D (p_set_cookie P C) T KE S w D0 sn0 (p_set_cookie P C) r0 S0 w0 h0.
Proof.
  unfold hcf5_same. intros (Hd & Hs & Hp & Hr & Hsh & Hk & Hh).
  repeat split; auto. apply hcf5_pr_eqb_refl.
Qed.

Lemma hcf5_p4_set_all P :
  hcf5_p4_setm (hcf5_p4_setd P (label_key cookie_label (hs_rstatic (p_hs P)))) (label_key mac1_label (hs_rstatic (p_hs P))) =
  p_set_cookie P (cookie_set_keys (p_cookie P) (hs_rstatic (p_hs P))).
Proof. reflexivity. Qed.

Section P4.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_P4_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) hcf5_P4
    (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HX. unfold hcf5_SX1, hcf5_Delta, hcf5_R, hcf5_P4. simplify_func_tycontext. abbreviate_semax.
  unfold hcf5_F, hcf5_Fx.
  Intros R S w D P T KE D0. Intros sn0 P0 r0 S0 w0 h0 RAW.
  unfold hcf5_core, hcf5_globs. cbn [app].
  pose proof H0 as Hinv. pose proof H1 as Hsame.
  destruct H0 as (Hrun & Hboot & Hw & Hdok & Hpok & Hslots & HTok & Hks).
  destruct H1 as (Hdev & Hsn & Hpr & Hr0 & Hsh & Hke & Hh0).
  rewrite (hcf5_pr_eqb_val _ _ Hpr).
  assert_PROP (@field_compatible CKS t_prsnap [] (l_ps0 L)) as Hfps by (go_lowerx; entailer!).
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_p L)) as Hfc.
  { go_lowerx. sep_apply (hcf5_p4_fc Tsh (l_p L) P). entailer!. }
  rewrite hcf5_p4_peer_split. repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, l_p L, p_hs P, p_cookie P).
  { go_lowerx. apply prop_right. destruct (l_p L); try contradiction; reflexivity. }
  assert (Hrs: hs_rstatic (p_hs P) = r_pub R) by apply Hpok.
  assert (Lpub: Zlength (r_pub R) = 32) by apply Hrun.
  rewrite Hrs.
  gather_SEP (hs_rep _ _ _) (cookie_rep _ _ _) (hcf5_p4_prest _ _ _). rewrite hcf5_p4_peer_join.
  gather_SEP (@data_at CKS _ t_prsnap _ _).
  remember (label_key cookie_label (r_pub R)) as kd eqn:Ekd.
  replace_SEP 0 (@data_at_ HCS Tsh (tarray tuchar 32) (hcf5_p4_dk (l_ps0 L)) *
   (@data_at HCS Tsh (tarray tuchar 32) (bytes kd) (hcf5_p4_dk (l_ps0 L)) -*
    @data_at CKS Tsh t_prsnap (prsnap_val (hcf5_p4_setd P kd)) (l_ps0 L)))%logic
    by (go_lowerx; rewrite sepcon_emp; apply hcf5_p4_psd).
  repeat flatten_sepcon_in_SEP.
  rewrite (hcf5_p4_ers_split (r_pub R) (l_pub L)).
  unfold hcf5_consts, wg_consts.
  change (hc_const gv ?i ?b) with (hbytes Ers b (gv i)).
  Intros.
  forward_call (gv, Tsh, hcf5_p4_dk (l_ps0 L), Ers, gv HGF5._x_config_any__M_LABEL_COOKIE, cookie_label, l_pub L, r_pub R).
  { go_lowerx. apply prop_right. unfold hcf5_p4_dk. rewrite !field_address_offset by auto with field_compatible.
    pose proof (field_compatible_isptr _ _ _ Hfps). destruct (l_ps0 L); try contradiction. simpl.
    rewrite Ptrofs.add_assoc. reflexivity. }
  rewrite <- Ekd.
  assert (Lkd: Zlength kd = 32) by (subst kd; apply hcf5_p4_label_len).
  gather_SEP (hbytes Tsh kd _) (_ -* _).
  replace_SEP 0 (@data_at CKS Tsh t_prsnap (prsnap_val (hcf5_p4_setd P kd)) (l_ps0 L))
    by (go_lowerx; rewrite sepcon_emp; unfold hbytes; rewrite Lkd; apply hcf5_p4_mp).
  gather_SEP (@data_at CKS _ t_prsnap _ _).
  remember (label_key mac1_label (r_pub R)) as km eqn:Ekm.
  replace_SEP 0 (@data_at_ HCS Tsh (tarray tuchar 32) (hcf5_p4_mk (l_ps0 L)) *
   (@data_at HCS Tsh (tarray tuchar 32) (bytes km) (hcf5_p4_mk (l_ps0 L)) -*
    @data_at CKS Tsh t_prsnap (prsnap_val (hcf5_p4_setm (hcf5_p4_setd P kd) km)) (l_ps0 L)))%logic
    by (go_lowerx; rewrite sepcon_emp; apply hcf5_p4_psm).
  repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, hcf5_p4_mk (l_ps0 L), Ers, gv HGF5._x_config_any__M_LABEL_MAC1, mac1_label, l_pub L, r_pub R).
  { go_lowerx. apply prop_right. unfold hcf5_p4_mk. rewrite !field_address_offset by auto with field_compatible.
    pose proof (field_compatible_isptr _ _ _ Hfps). destruct (l_ps0 L); try contradiction. simpl.
    rewrite Ptrofs.add_assoc. reflexivity. }
  rewrite <- Ekm.
  assert (Lkm: Zlength km = 32) by (subst km; apply hcf5_p4_label_len).
  gather_SEP (hbytes Tsh km _) (_ -* _).
  replace_SEP 0 (@data_at CKS Tsh t_prsnap (prsnap_val (hcf5_p4_setm (hcf5_p4_setd P kd) km)) (l_ps0 L))
    by (go_lowerx; rewrite sepcon_emp; unfold hbytes; rewrite Lkm; apply hcf5_p4_mp).
  replace (hcf5_p4_setm (hcf5_p4_setd P kd) km) with (p_set_cookie P (cookie_set_keys (p_cookie P) (r_pub R)))
    by (subst kd km; reflexivity).
  gather_SEP (hbytes Ers (r_pub R) _) (hbytes (Share.comp Ers) (r_pub R) _).
  rewrite <- hcf5_p4_ers_split.
  pose proof (hcf5_p4_inv _ _ _ _ _ _ _ _ _ (cookie_set_keys (p_cookie P) (r_pub R)) Hinv) as Hinv'.
  pose proof (hcf5_p4_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cookie_set_keys (p_cookie P) (r_pub R)) Hsame) as Hsame'.
  set (P' := p_set_cookie P (cookie_set_keys (p_cookie P) (r_pub R))) in *.
  Exists R S w D P' T KE D0.
  Exists sn0 P' r0 S0 w0 h0 RAW.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_consts, wg_consts. cbn [app].
  go_lowerx. entailer!.
  unfold hc_const, hbytes. cancel.
Qed.

End P4.
