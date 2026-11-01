(* (group snap of common4): the comparison bodies dev_same, skb_same. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require VST.floyd.VSU.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4b_snap_vobjs.
Require Import WgNoise.proof.harness.common4.hc4b_snap_cmp.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Module FD := WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance CS4.
#[local] Instance hc4b_dev_i1 : change_composite_env CKS CS4. make_cs_preserve CKS CS4. Defined.
#[local] Instance hc4b_dev_i3 : change_composite_env Noise.CS CS4. make_cs_preserve Noise.CS CS4. Defined.
#[local] Instance hc4b_dev_i4 : change_composite_env CS4 Noise.CS. make_cs_preserve CS4 Noise.CS. Defined.

Require WgNoise.proof.harness.common.hc3_body_ck.

(* byte arrays as hbytes *)
Lemma hc4b_dev_hb {cs: compspecs} sh (bs: list byte) n p : Zlength bs = n ->
  @data_at cs sh (tarray tuchar n) (bytes bs) p = hbytes sh bs p.
Proof.
  intros <-. unfold hbytes. apply WgNoise.proof.harness.common.hc3_body_ck.hc3b_ck_data_at_cs.
Qed.

Definition hc4b_dvf (sh: share) (wg: val) (D: device) (lk1 lk2: val) : mpred :=
  field_at sh t_dev (DOT FD._dev) (d_dev D) wg *
  hbytes sh (id_pub (d_id D)) (field_address t_dev (DOT FD._static_identity DOT FD._static_public) wg) *
  hbytes sh (id_priv (d_id D)) (field_address t_dev (DOT FD._static_identity DOT FD._static_private) wg) *
  field_at sh t_dev (DOT FD._static_identity DOT FD._lock) lk1 wg *
  field_at sh t_dev (DOT FD._static_identity DOT FD._has_identity) (Val.of_bool (id_has (d_id D))) wg *
  spacer sh 77 80 wg *
  hbytes sh (cc_secret (d_cc D)) (field_address t_dev (DOT FD._cookie_checker DOT FD._secret) wg) *
  hbytes sh (cc_ekey (d_cc D)) (field_address t_dev (DOT FD._cookie_checker DOT FD._cookie_encryption_key) wg) *
  hbytes sh (cc_mkey (d_cc D)) (field_address t_dev (DOT FD._cookie_checker DOT FD._message_mac1_key) wg) *
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._secret_birthdate) (Vlong (cc_birth (d_cc D))) wg *
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._secret_lock) lk2 wg *
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._device) (cc_dev (d_cc D)) wg * spacer sh 188 192 wg *
  field_at sh t_dev (DOT FD._peer_hashtable) (d_ptab D) wg *
  field_at sh t_dev (DOT FD._index_hashtable) (d_itab D) wg.

Lemma hc4b_dev_sid sh wg (v: reptype t_sid) : field_compatible t_dev [] wg ->
  @data_at Noise.CS sh t_sid v (id_addr wg) = field_at sh t_dev (DOT FD._static_identity) v wg.
Proof.
  intros FC. rewrite (@data_at_change_composite Noise.CS CS4 _ sh t_sid _ _ (JMeq_refl _)) by reflexivity.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma hc4b_dev_cc sh wg (v: reptype t_cc) : field_compatible t_dev [] wg ->
  @data_at Noise.CS sh t_cc v (cc_addr wg) = field_at sh t_dev (DOT FD._cookie_checker) v wg.
Proof.
  intros FC. rewrite (@data_at_change_composite Noise.CS CS4 _ sh t_cc _ _ (JMeq_refl _)) by reflexivity.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma hc4b_dev_split_sid sh wg (a b: list val) (lk h: val) :
  field_at sh t_dev (DOT FD._static_identity) (a, (b, (lk, h))) wg =
  field_at sh t_dev (DOT FD._static_identity DOT FD._static_public) a wg *
  field_at sh t_dev (DOT FD._static_identity DOT FD._static_private) b wg *
  field_at sh t_dev (DOT FD._static_identity DOT FD._lock) lk wg *
  field_at sh t_dev (DOT FD._static_identity DOT FD._has_identity) h wg *
  spacer sh 77 80 wg.
Proof.
  unfold_field_at (field_at _ _ (DOT FD._static_identity) _ _).
  apply pred_ext; cancel.
Qed.

Lemma hc4b_dev_split_cc sh wg (a b c: list val) (bi lk d: val) :
  field_at sh t_dev (DOT FD._cookie_checker) (a, (b, (c, (bi, (lk, d))))) wg =
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._secret) a wg *
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._cookie_encryption_key) b wg *
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._message_mac1_key) c wg *
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._secret_birthdate) bi wg *
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._secret_lock) lk wg *
  field_at sh t_dev (DOT FD._cookie_checker DOT FD._device) d wg * spacer sh 188 192 wg.
Proof.
  unfold_field_at (field_at _ _ (DOT FD._cookie_checker) _ _).
  apply pred_ext; cancel.
Qed.

Ltac hc4b_dev_open FC4 :=
  rewrite (@field_at_change_composite Noise.CS CS4 _ _ t_dev (DOT FD._dev) _ _ (JMeq_refl _)) by reflexivity;
  rewrite (@field_at_change_composite Noise.CS CS4 _ _ t_dev (DOT FD._peer_hashtable) _ _ (JMeq_refl _)) by reflexivity;
  rewrite (@field_at_change_composite Noise.CS CS4 _ _ t_dev (DOT FD._index_hashtable) _ _ (JMeq_refl _)) by reflexivity;
  rewrite (hc4b_dev_sid _ _ _ FC4), (hc4b_dev_cc _ _ _ FC4);
  rewrite hc4b_dev_split_sid, hc4b_dev_split_cc;
  rewrite (field_at_data_at _ t_dev (DOT FD._static_identity DOT FD._static_public)),
    (field_at_data_at _ t_dev (DOT FD._static_identity DOT FD._static_private)),
    (field_at_data_at _ t_dev (DOT FD._cookie_checker DOT FD._secret)),
    (field_at_data_at _ t_dev (DOT FD._cookie_checker DOT FD._cookie_encryption_key)),
    (field_at_data_at _ t_dev (DOT FD._cookie_checker DOT FD._message_mac1_key));
  simpl nested_field_type.

Lemma hc4b_dev_eq sh wg D :
  device_rep sh wg D =
  !! (@field_compatible Noise.CS t_dev [] wg /\ id_ok (d_id D) /\ cc_ok (d_cc D)) &&
  EX lk1: val, EX lk2: val, hc4b_dvf sh wg D lk1 lk2.
Proof.
  unfold device_rep, identity_rep, checker_rep, hc4b_dvf.
  apply pred_ext.
  - Intros lk1 lk2. Exists lk2 lk1.
    assert (FC4: field_compatible t_dev [] wg) by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_dev); auto).
    match goal with H: id_ok _ |- _ => destruct H as (I1 & I2) end.
    match goal with H: cc_ok _ |- _ => destruct H as (C1 & C2 & C3) end.
    hc4b_dev_open FC4.
    rewrite !(hc4b_dev_hb sh _ 32) by assumption.
    entailer!; repeat split; auto.
  - Intros lk1 lk2.
    assert (FC4: field_compatible t_dev [] wg) by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_dev); auto).
    match goal with H: id_ok _ |- _ => destruct H as (I1 & I2) end.
    match goal with H: cc_ok _ |- _ => destruct H as (C1 & C2 & C3) end.
    Exists lk2 lk1.
    hc4b_dev_open FC4.
    rewrite !(hc4b_dev_hb sh _ 32) by assumption.
    entailer!; repeat split; auto.
Qed.

Lemma hc4b_dev_len sh (bs: list byte) p n : 0 <= n ->
  data_at sh (tarray tuchar n) (bytes bs) p |-- !! (Zlength bs = n).
Proof.
  intros N. entailer!. unfold bytes. rewrite Zlength_map. reflexivity.
Qed.

Definition hc4b_dsf (sh: share) (s: val) (D: device) (h: val) : mpred :=
  field_at sh t_devsnap (DOT FD._dev) (d_dev D) s *
  data_at sh (tarray tuchar 32) (bytes (id_pub (d_id D))) (@field_address CKS t_devsnap (DOT FD._static_public) s) *
  data_at sh (tarray tuchar 32) (bytes (id_priv (d_id D))) (@field_address CKS t_devsnap (DOT FD._static_private) s) *
  field_at sh t_devsnap (DOT FD._has_identity) (Val.of_bool (id_has (d_id D))) s *
  data_at sh (tarray tuchar 32) (bytes (cc_secret (d_cc D))) (@field_address CKS t_devsnap (DOT FD._secret) s) * spacer sh 105 112 s *
  field_at sh t_devsnap (DOT FD._secret_birthdate) (Vlong (cc_birth (d_cc D))) s *
  data_at sh (tarray tuchar 32) (bytes (cc_ekey (d_cc D))) (@field_address CKS t_devsnap (DOT FD._cookie_encryption_key) s) *
  data_at sh (tarray tuchar 32) (bytes (cc_mkey (d_cc D))) (@field_address CKS t_devsnap (DOT FD._message_mac1_key) s) *
  field_at sh t_devsnap (DOT FD._checker_device) (cc_dev (d_cc D)) s *
  field_at sh t_devsnap (DOT FD._peer_hashtable) (d_ptab D) s *
  field_at sh t_devsnap (DOT FD._index_hashtable) (d_itab D) s *
  field_at sh t_devsnap (DOT FD._peers_head) h s.

Ltac hc4b_dcc f := rewrite (@field_at_change_composite CKS CS4 _ _ t_devsnap (DOT f) _ _ (JMeq_refl _)) by reflexivity.
Ltac hc4b_dar f := rewrite (@field_at_data_at CKS _ t_devsnap (DOT f)).

Lemma hc4b_dev_snap_eq sh s D h : @data_at CKS sh t_devsnap (devsnap_val D h) s = hc4b_dsf sh s D h.
Proof.
  unfold devsnap_val. unfold_data_at (@data_at CKS _ _ _ s).
  hc4b_dar FD._static_public. hc4b_dar FD._static_private. hc4b_dar FD._secret.
  hc4b_dar FD._cookie_encryption_key. hc4b_dar FD._message_mac1_key.
  simpl nested_field_type.
  rewrite !(@WgNoise.proof.harness.common.hc3_body_ck.hc3b_ck_data_at_cs CKS CS4).
  hc4b_dcc FD._dev. hc4b_dcc FD._has_identity. hc4b_dcc FD._secret_birthdate. hc4b_dcc FD._checker_device.
  hc4b_dcc FD._peer_hashtable. hc4b_dcc FD._index_hashtable. hc4b_dcc FD._peers_head.
  unfold hc4b_dsf. apply pred_ext; cancel.
Qed.

Lemma hc4b_dev_fa s f : @field_compatible CKS t_devsnap [] s ->
  In f [FD._static_public; FD._static_private; FD._secret; FD._cookie_encryption_key; FD._message_mac1_key] ->
  @field_address CKS t_devsnap (DOT f) s = @field_address CS4 t_devsnap (DOT f) s.
Proof.
  intros FC Hf. assert (FC4: @field_compatible CS4 t_devsnap [] s)
    by (apply (@field_compatible_change_composite CKS CS4 _ t_devsnap); auto).
  destruct Hf as [<- | [<- | [<- | [<- | [<- | []]]]]];
  rewrite (@field_address_offset CKS), (@field_address_offset CS4) by auto with field_compatible; reflexivity.
Qed.

(* valid pointers of dev_same: NULL, wg, the public-key table, lent *)
Lemma hc4b_dev_vp CSw sh wg (d: val) shp tab (h: val) VO x R :
  readable_share sh -> readable_share shp -> Forall vobj_ok VO ->
  (x = nullval \/ x = wg \/ x = tab \/ In x (hc4b_vobjs_vaddrs VO)) ->
  @field_at CS4 sh t_dev (DOT FD._dev) d wg * @data_at CS4 shp t_ptab h tab * vobjs CSw VO * R |-- valid_pointer x.
Proof.
  intros RS RP HF Hx.
  apply derives_trans with (vobjs CSw VO * (@field_at CS4 sh t_dev (DOT FD._dev) d wg * @data_at CS4 shp t_ptab h tab * R));
    [cancel|].
  apply (hc4b_vp_ok CSw VO [wg; tab]); auto.
  - destruct Hx as [? | [-> | [-> | ?]]]; simpl; tauto.
  - intros [<- | [<- | []]].
    + apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
      rewrite (@field_at_change_composite CS4 Noise.CS _ sh t_dev (DOT FD._dev) _ _ (JMeq_refl _)) by reflexivity.
      apply (@field_at_valid_ptr0 Noise.CS); [auto | simpl; lia | reflexivity].
    + apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
      apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4b_dev_pn CSw sh wg (d: val) shp tab (h: val) VO x R :
  readable_share sh -> readable_share shp -> Forall vobj_ok VO ->
  (x = nullval \/ x = wg \/ x = tab \/ In x (hc4b_vobjs_vaddrs VO)) ->
  @field_at CS4 sh t_dev (DOT FD._dev) d wg * @data_at CS4 shp t_ptab h tab * vobjs CSw VO * R |-- !! is_pointer_or_null x.
Proof.
  intros. eapply derives_trans; [apply hc4b_dev_vp; eauto|]. apply VST.floyd.VSU.valid_pointer_is_null_or_ptr.
Qed.

Ltac hc4b_dev_vp_tac HVA CSw sh wg d shp tab h VO :=
  apply denote_tc_test_eq_split;
  (eapply derives_trans; [| apply (hc4b_dev_vp CSw sh wg d shp tab h VO _ TT);
                            [assumption | assumption | assumption | apply HVA; simpl; tauto]];
   cancel).

Ltac hc4b_dev_params :=
  match goal with |- context [Vlong (Int64.repr (Zlength ?A))] =>
    let E := fresh in assert (E: Zlength A = 32) by assumption; rewrite E end;
  simpl; rewrite !field_address_offset by auto with field_compatible;
  rewrite ?offset_offset_val; simpl; reflexivity.

Lemma hc4b_dev_same CSw
  (HV: forall VO x, In x (vobjs_addrs VO) -> In x (hc4b_vobjs_vaddrs VO)) :
  @semax_body [] hc4_G_dev_same CS4 FD.f_dev_same (dev_same4_spec CSw).
Proof.
  start_function.
  rename H into HVO. rename H0 into HPP.
  assert (HVA: forall x, In x (dev_ptrs D0 h0 D head) ->
            x = nullval \/ x = wg \/ x = d_ptab D \/ In x (hc4b_vobjs_vaddrs VO)).
  { intros x Hx. rewrite Forall_forall in HPP. destruct (HPP x Hx) as [? | [? | [? | ?]]];
    [left; auto | right; left; auto | right; right; left; auto | right; right; right; auto]. }
  assert_PROP (@field_compatible CKS t_devsnap [] s) as FCs by entailer!.
  rewrite hc4b_dev_eq. Intros lk1 lk2. unfold hc4b_dvf.
  match goal with H: id_ok _ |- _ => destruct H as (I1 & I2) end.
  match goal with H: cc_ok _ |- _ => destruct H as (C1 & C2 & C3) end.
  assert (Ps: isptr s) by (destruct FCs; auto).
  assert (Pwg: isptr wg) by (match goal with H: @field_compatible _ t_dev [] wg |- _ => destruct H; auto end).
  assert (FCs4: @field_compatible CS4 t_devsnap [] s)
    by (apply (@field_compatible_change_composite CKS CS4 _ t_devsnap); auto).
  assert (FCw4: @field_compatible CS4 t_dev [] wg)
    by (match goal with H: @field_compatible ?cs t_dev [] wg |- _ =>
          apply (@field_compatible_change_composite cs CS4 _ t_dev); auto end).
  unfold ptable. rewrite (@data_at_change_composite Noise.CS CS4 _ shp t_ptab _ _ (JMeq_refl _)) by reflexivity.
  rewrite hc4b_dev_snap_eq. unfold hc4b_dsf.
  rewrite !hc4b_dev_fa by (auto; simpl; tauto).
  assert_PROP (Zlength (id_pub (d_id D0)) = 32 /\ Zlength (id_priv (d_id D0)) = 32 /\
               Zlength (cc_secret (d_cc D0)) = 32 /\ Zlength (cc_ekey (d_cc D0)) = 32 /\
               Zlength (cc_mkey (d_cc D0)) = 32) as JJ.
  { entailer!. unfold bytes in *. rewrite !Zlength_map in *. auto. }
  destruct JJ as (J1 & J2 & J3 & J4 & J5).
  rewrite !(hc4b_dev_hb shs _ 32) by assumption.
  assert_PROP (Forall is_pointer_or_null (dev_ptrs D0 h0 D head)) as PN.
  { go_lowerx. apply hc4b_cmp_forall_prop. intros x Hx.
    eapply derives_trans; [| apply (hc4b_dev_pn CSw shd wg (d_dev D) shp (d_ptab D) head VO x TT); auto].
    cancel. }
  unfold dev_ptrs in PN. rewrite Forall_forall in PN.
  assert (N1 := PN (d_dev D0) ltac:(simpl; tauto)). assert (N2 := PN (d_dev D) ltac:(simpl; tauto)).
  assert (N3 := PN (cc_dev (d_cc D0)) ltac:(simpl; tauto)). assert (N4 := PN (cc_dev (d_cc D)) ltac:(simpl; tauto)).
  assert (N5 := PN (d_ptab D0) ltac:(simpl; tauto)). assert (N6 := PN (d_ptab D) ltac:(simpl; tauto)).
  assert (N7 := PN (d_itab D0) ltac:(simpl; tauto)). assert (N8 := PN (d_itab D) ltac:(simpl; tauto)).
  assert (N9 := PN h0 ltac:(simpl; tauto)). assert (N10 := PN head ltac:(simpl; tauto)).
  clear PN.
  Intros.
  forward. forward.
  forward_if (temp FD._t'1 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D))))).
  { hc4b_dev_vp_tac HVA CSw shd wg (d_dev D) shp (d_ptab D) head VO. }
  { forward_call (shs, @field_address CS4 t_devsnap (DOT FD._static_public) s, id_pub (d_id D0), shd, @field_address CS4 t_dev (DOT FD._static_identity DOT FD._static_public) wg, id_pub (d_id D)).
    { entailer!. hc4b_dev_params. }
    forward. entailer!. unfold veqb. rewrite if_true by auto. cbn [andb].
    match goal with |- context [bytes_eqb ?a ?b] => destruct (bytes_eqb a b) end; reflexivity. }
  { forward. entailer!. unfold veqb. rewrite if_false by auto. reflexivity. }
  forward_if (temp FD._t'3 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D))))).
  { forward_call (shs, @field_address CS4 t_devsnap (DOT FD._static_private) s, id_priv (d_id D0), shd, @field_address CS4 t_dev (DOT FD._static_identity DOT FD._static_private) wg, id_priv (d_id D)).
    { entailer!. hc4b_dev_params. }
    forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'5 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D))))).
  { forward. { entailer!. destruct (id_has (d_id D0)); hnf; auto. }
    forward. { entailer!. destruct (id_has (d_id D)); hnf; auto. }
    forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'6 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) && bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D))))).
  { forward_call (shs, @field_address CS4 t_devsnap (DOT FD._secret) s, cc_secret (d_cc D0), shd, @field_address CS4 t_dev (DOT FD._cookie_checker DOT FD._secret) wg, cc_secret (d_cc D)).
    { entailer!. hc4b_dev_params. }
    forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'8 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) && bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D)) && Int64.eq (cc_birth (d_cc D0)) (cc_birth (d_cc D))))).
  { forward. forward. forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'9 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) && bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D)) && Int64.eq (cc_birth (d_cc D0)) (cc_birth (d_cc D)) && bytes_eqb (cc_ekey (d_cc D0)) (cc_ekey (d_cc D))))).
  { forward_call (shs, @field_address CS4 t_devsnap (DOT FD._cookie_encryption_key) s, cc_ekey (d_cc D0), shd, @field_address CS4 t_dev (DOT FD._cookie_checker DOT FD._cookie_encryption_key) wg, cc_ekey (d_cc D)).
    { entailer!. hc4b_dev_params. }
    forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'11 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) && bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D)) && Int64.eq (cc_birth (d_cc D0)) (cc_birth (d_cc D)) && bytes_eqb (cc_ekey (d_cc D0)) (cc_ekey (d_cc D)) && bytes_eqb (cc_mkey (d_cc D0)) (cc_mkey (d_cc D))))).
  { forward_call (shs, @field_address CS4 t_devsnap (DOT FD._message_mac1_key) s, cc_mkey (d_cc D0), shd, @field_address CS4 t_dev (DOT FD._cookie_checker DOT FD._message_mac1_key) wg, cc_mkey (d_cc D)).
    { entailer!. hc4b_dev_params. }
    forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'13 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) && bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D)) && Int64.eq (cc_birth (d_cc D0)) (cc_birth (d_cc D)) && bytes_eqb (cc_ekey (d_cc D0)) (cc_ekey (d_cc D)) && bytes_eqb (cc_mkey (d_cc D0)) (cc_mkey (d_cc D)) && veqb (cc_dev (d_cc D0)) (cc_dev (d_cc D))))).
  { forward. forward. forward. { entailer!. hc4b_dev_vp_tac HVA CSw shd wg (d_dev D) shp (d_ptab D) head VO. } hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'14 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) && bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D)) && Int64.eq (cc_birth (d_cc D0)) (cc_birth (d_cc D)) && bytes_eqb (cc_ekey (d_cc D0)) (cc_ekey (d_cc D)) && bytes_eqb (cc_mkey (d_cc D0)) (cc_mkey (d_cc D)) && veqb (cc_dev (d_cc D0)) (cc_dev (d_cc D)) && veqb (d_ptab D0) (d_ptab D)))).
  { forward. forward. forward. { entailer!. hc4b_dev_vp_tac HVA CSw shd wg (d_dev D) shp (d_ptab D) head VO. } hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'15 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) && bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D)) && Int64.eq (cc_birth (d_cc D0)) (cc_birth (d_cc D)) && bytes_eqb (cc_ekey (d_cc D0)) (cc_ekey (d_cc D)) && bytes_eqb (cc_mkey (d_cc D0)) (cc_mkey (d_cc D)) && veqb (cc_dev (d_cc D0)) (cc_dev (d_cc D)) && veqb (d_ptab D0) (d_ptab D) && veqb (d_itab D0) (d_itab D)))).
  { forward. forward. forward. { entailer!. hc4b_dev_vp_tac HVA CSw shd wg (d_dev D) shp (d_ptab D) head VO. } hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FD._t'16 (Val.of_bool (veqb (d_dev D0) (d_dev D) && bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) && Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) && bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D)) && Int64.eq (cc_birth (d_cc D0)) (cc_birth (d_cc D)) && bytes_eqb (cc_ekey (d_cc D0)) (cc_ekey (d_cc D)) && bytes_eqb (cc_mkey (d_cc D0)) (cc_mkey (d_cc D)) && veqb (cc_dev (d_cc D0)) (cc_dev (d_cc D)) && veqb (d_ptab D0) (d_ptab D) && veqb (d_itab D0) (d_itab D) && veqb h0 head))).
  { forward. forward. forward. forward. { entailer!. hc4b_dev_vp_tac HVA CSw shd wg (d_dev D) shp (d_ptab D) head VO. } hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward.
  rewrite hc4b_dev_eq. Exists lk1 lk2. unfold hc4b_dvf.
  unfold ptable. rewrite (@data_at_change_composite Noise.CS CS4 _ shp t_ptab _ _ (JMeq_refl _)) by reflexivity.
  rewrite hc4b_dev_snap_eq. unfold hc4b_dsf.
  rewrite !hc4b_dev_fa by (auto; simpl; tauto).
  rewrite !(hc4b_dev_hb shs _ 32) by assumption.
  entailer!.
  split; [| unfold id_ok, cc_ok; auto].
  unfold dev_eqb. match goal with |- Val.of_bool ?X = _ => destruct X; reflexivity end.
Qed.
