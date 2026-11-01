(* (group snap of common4) child part: the snapshot bodies pr_take, dev_take,
   skb_take. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.

Require WgNoise.proof.harness.common.hc3_body_ck.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Local Open Scope logic.

Module FT := WgNoise.harness.x_cookie_mac.code.

(* ------------------------------------------------------------------------------------------------ *)
(* skb_take                                                                                         *)
(* ------------------------------------------------------------------------------------------------ *)

Section SKB.
#[local] Existing Instance CS4skb.
#[local] Instance hc4bt_skb_i1 : change_composite_env CKS CS4skb. make_cs_preserve CKS CS4skb. Defined.
#[local] Instance hc4bt_skb_i2 : change_composite_env Cookie.CS CS4skb. make_cs_preserve Cookie.CS CS4skb. Defined.

Lemma hc4bt_skb_snap_split sh s (a l pr: val) (b4 b16 b2: list val) :
  @data_at CS4skb sh t_skbsnap (a, (l, (pr, (b4, (b16, b2))))) s =
  field_at sh t_skbsnap (DOT FT._data) a s * field_at sh t_skbsnap (DOT FT._len) l s *
  field_at sh t_skbsnap (DOT FT._protocol) pr s *
  data_at sh (tarray tuchar 4) b4 (field_address t_skbsnap (DOT FT._saddr4) s) *
  data_at sh (tarray tuchar 16) b16 (field_address t_skbsnap (DOT FT._saddr6) s) *
  data_at sh (tarray tuchar 2) b2 (field_address t_skbsnap (DOT FT._sport) s) *
  spacer sh 36 40 s.
Proof.
  unfold_data_at (data_at _ _ _ s).
  rewrite (field_at_data_at _ t_skbsnap (DOT FT._saddr4)), (field_at_data_at _ t_skbsnap (DOT FT._saddr6)),
    (field_at_data_at _ t_skbsnap (DOT FT._sport)).
  simpl nested_field_type. apply pred_ext; cancel.
Qed.

Lemma hc4bt_skb_skb_split sh p (a l pr: val) (b4 b16 b2: list val) :
  @data_at CS4skb sh t_skb (a, (l, (pr, (b4, (b16, b2))))) p =
  field_at sh t_skb (DOT FT._data) a p * field_at sh t_skb (DOT FT._len) l p *
  field_at sh t_skb (DOT FT._protocol) pr p *
  data_at sh (tarray tuchar 4) b4 (field_address t_skb (DOT FT._ip4 DOT FT._saddr DOT FT._s_addr) p) *
  data_at sh (tarray tuchar 16) b16 (field_address t_skb (DOT FT._ip6 DOT FT._saddr DOT FT._s6_addr) p) *
  data_at sh (tarray tuchar 2) b2 (field_address t_skb (DOT FT._udp DOT FT._source) p) *
  spacer sh 36 40 p.
Proof.
  unfold_data_at (data_at _ _ _ p).
  unfold_field_at 4%nat. unfold_field_at 4%nat. unfold_field_at 5%nat. unfold_field_at 5%nat.
  unfold_field_at 6%nat.
  rewrite (field_at_data_at _ t_skb (DOT FT._ip4 DOT FT._saddr DOT FT._s_addr)),
    (field_at_data_at _ t_skb (DOT FT._ip6 DOT FT._saddr DOT FT._s6_addr)),
    (field_at_data_at _ t_skb (DOT FT._udp DOT FT._source)).
  simpl nested_field_type. apply pred_ext; cancel.
Qed.

Lemma hc4bt_hb {cs: compspecs} sh (bs: list byte) n p : Zlength bs = n ->
  @data_at cs sh (tarray tuchar n) (bytes bs) p = hbytes sh bs p.
Proof.
  intros <-. unfold hbytes. apply WgNoise.proof.harness.common.hc3_body_ck.hc3b_ck_data_at_cs.
Qed.

Lemma hc4bt_ho {cs: compspecs} sh n p :
  @data_at cs sh (tarray tuchar n) (Zrepeat Vundef n) p = hout sh n p.
Proof.
  unfold hout. rewrite (@WgNoise.proof.harness.common.hc3_body_ck.hc3b_ck_data_at__cs HCS cs). reflexivity.
Qed.

Lemma hc4bt_ze p : 0 <= p <= 65535 -> Int.zero_ext 16 (Int.repr p) = Int.repr p.
Proof.
  intros Hp.
  assert (E: Int.unsigned (Int.zero_ext 16 (Int.repr p)) = Int.unsigned (Int.repr p)).
  { rewrite Int.zero_ext_mod by (cbn; lia). rewrite Int.unsigned_repr by rep_lia.
    apply Z.mod_small. change (two_p 16) with 65536. lia. }
  rewrite <- (Int.repr_unsigned (Int.zero_ext 16 (Int.repr p))), E, Int.repr_unsigned. reflexivity.
Qed.

Ltac hc4bt_params :=
  simpl; rewrite ?field_address_offset by auto with field_compatible;
  rewrite ?offset_offset_val; simpl; try reflexivity.

Lemma hc4bt_skb_take :
  @semax_body [] hc4_G_dev_take CS4skb FT.f_skb_take skb_take4_spec.
Proof.
  start_function.
  unfold skb_rep. Intros.
  match goal with H: skb_ok sk |- _ => destruct H as (Pk & L4 & L6 & L2) end.
  rewrite (@data_at__change_composite CKS CS4skb _ shs t_skbsnap) by reflexivity.
  rewrite (@data_at_change_composite Cookie.CS CS4skb _ shk t_skb _ _ (JMeq_refl _)) by reflexivity.
  assert_PROP (@field_compatible CS4skb t_skbsnap [] s /\ @field_compatible CS4skb t_skb [] sp) as FC by entailer!.
  destruct FC as [FCs FCp].
  change (@data_at_ CS4skb shs t_skbsnap s) with (@data_at CS4skb shs t_skbsnap
    (Vundef, (Vundef, (Vundef, (Zrepeat Vundef 4, (Zrepeat Vundef 16, Zrepeat Vundef 2))))) s).
  unfold skb_val. rewrite hc4bt_skb_snap_split, hc4bt_skb_skb_split.
  assert (Ps: isptr s) by (destruct FCs; auto). assert (Psp: isptr sp) by (destruct FCp; auto).
  rewrite !hc4bt_ho. rewrite (hc4bt_hb shk _ 4) by assumption. rewrite (hc4bt_hb shk _ 16) by assumption.
  rewrite (hc4bt_hb shk _ 2) by assumption.
  Intros. forward. { entailer!. match goal with T: tc_val' _ (sk_data sk) |- _ => apply T; auto end. }
  forward. forward. forward. forward. { entailer!. lia. }
  forward.
  replace (hout shs 4 (field_address t_skbsnap (DOT FT._saddr4) s))
    with (hout shs (Zlength (sk_ip4 sk)) (field_address t_skbsnap (DOT FT._saddr4) s)) by (rewrite L4; reflexivity).
  forward_call (shs, field_address t_skbsnap (DOT FT._saddr4) s, shk,
                field_address t_skb (DOT FT._ip4 DOT FT._saddr DOT FT._s_addr) sp, sk_ip4 sk).
  { entailer!. rewrite L4. hc4bt_params. }
  replace (hout shs 16 (field_address t_skbsnap (DOT FT._saddr6) s))
    with (hout shs (Zlength (sk_ip6 sk)) (field_address t_skbsnap (DOT FT._saddr6) s)) by (rewrite L6; reflexivity).
  forward_call (shs, field_address t_skbsnap (DOT FT._saddr6) s, shk,
                field_address t_skb (DOT FT._ip6 DOT FT._saddr DOT FT._s6_addr) sp, sk_ip6 sk).
  { entailer!. rewrite L6. hc4bt_params. }
  replace (hout shs 2 (field_address t_skbsnap (DOT FT._sport) s))
    with (hout shs (Zlength (sk_port sk)) (field_address t_skbsnap (DOT FT._sport) s)) by (rewrite L2; reflexivity).
  forward_call (shs, field_address t_skbsnap (DOT FT._sport) s, shk,
                field_address t_skb (DOT FT._udp DOT FT._source) sp, sk_port sk).
  { entailer!. rewrite L2. hc4bt_params. }
  forward.
  unfold skb_rep, skbsnap_val, skb_val.
  rewrite (@data_at_change_composite CKS CS4skb _ shs t_skbsnap _ _ (JMeq_refl _)) by reflexivity.
  rewrite (@data_at_change_composite Cookie.CS CS4skb _ shk t_skb _ _ (JMeq_refl _)) by reflexivity.
  rewrite hc4bt_skb_snap_split, hc4bt_skb_skb_split.
  rewrite (hc4bt_hb shs _ 4) by assumption. rewrite (hc4bt_hb shs _ 16) by assumption.
  rewrite (hc4bt_hb shs _ 2) by assumption.
  rewrite (hc4bt_hb shk _ 4) by assumption. rewrite (hc4bt_hb shk _ 16) by assumption.
  rewrite (hc4bt_hb shk _ 2) by assumption.
  entailer!. unfold skb_ok; auto.
Qed.
End SKB.

(* ------------------------------------------------------------------------------------------------ *)
(* dev_take                                                                                         *)
(* ------------------------------------------------------------------------------------------------ *)

Section DEV.
#[local] Existing Instance CS4.
#[local] Instance hc4bt_dev_i1 : change_composite_env CKS CS4. make_cs_preserve CKS CS4. Defined.
#[local] Instance hc4bt_dev_i3 : change_composite_env Noise.CS CS4. make_cs_preserve Noise.CS CS4. Defined.
#[local] Instance hc4bt_dev_i4 : change_composite_env CS4 Noise.CS. make_cs_preserve CS4 Noise.CS. Defined.

Definition hc4bt_dvf (sh: share) (wg: val) (D: device) (lk1 lk2: val) : mpred :=
  field_at sh t_dev (DOT FT._dev) (d_dev D) wg *
  hbytes sh (id_pub (d_id D)) (field_address t_dev (DOT FT._static_identity DOT FT._static_public) wg) *
  hbytes sh (id_priv (d_id D)) (field_address t_dev (DOT FT._static_identity DOT FT._static_private) wg) *
  field_at sh t_dev (DOT FT._static_identity DOT FT._lock) lk1 wg *
  field_at sh t_dev (DOT FT._static_identity DOT FT._has_identity) (Val.of_bool (id_has (d_id D))) wg *
  spacer sh 77 80 wg *
  hbytes sh (cc_secret (d_cc D)) (field_address t_dev (DOT FT._cookie_checker DOT FT._secret) wg) *
  hbytes sh (cc_ekey (d_cc D)) (field_address t_dev (DOT FT._cookie_checker DOT FT._cookie_encryption_key) wg) *
  hbytes sh (cc_mkey (d_cc D)) (field_address t_dev (DOT FT._cookie_checker DOT FT._message_mac1_key) wg) *
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._secret_birthdate) (Vlong (cc_birth (d_cc D))) wg *
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._secret_lock) lk2 wg *
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._device) (cc_dev (d_cc D)) wg * spacer sh 188 192 wg *
  field_at sh t_dev (DOT FT._peer_hashtable) (d_ptab D) wg *
  field_at sh t_dev (DOT FT._index_hashtable) (d_itab D) wg.

Lemma hc4bt_dev_sid sh wg (v: reptype t_sid) : field_compatible t_dev [] wg ->
  @data_at Noise.CS sh t_sid v (id_addr wg) = field_at sh t_dev (DOT FT._static_identity) v wg.
Proof.
  intros FC. rewrite (@data_at_change_composite Noise.CS CS4 _ sh t_sid _ _ (JMeq_refl _)) by reflexivity.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma hc4bt_dev_cc sh wg (v: reptype t_cc) : field_compatible t_dev [] wg ->
  @data_at Noise.CS sh t_cc v (cc_addr wg) = field_at sh t_dev (DOT FT._cookie_checker) v wg.
Proof.
  intros FC. rewrite (@data_at_change_composite Noise.CS CS4 _ sh t_cc _ _ (JMeq_refl _)) by reflexivity.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma hc4bt_dev_split_sid sh wg (a b: list val) (lk h: val) :
  field_at sh t_dev (DOT FT._static_identity) (a, (b, (lk, h))) wg =
  field_at sh t_dev (DOT FT._static_identity DOT FT._static_public) a wg *
  field_at sh t_dev (DOT FT._static_identity DOT FT._static_private) b wg *
  field_at sh t_dev (DOT FT._static_identity DOT FT._lock) lk wg *
  field_at sh t_dev (DOT FT._static_identity DOT FT._has_identity) h wg *
  spacer sh 77 80 wg.
Proof.
  unfold_field_at (field_at _ _ (DOT FT._static_identity) _ _).
  apply pred_ext; cancel.
Qed.

Lemma hc4bt_dev_split_cc sh wg (a b c: list val) (bi lk d: val) :
  field_at sh t_dev (DOT FT._cookie_checker) (a, (b, (c, (bi, (lk, d))))) wg =
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._secret) a wg *
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._cookie_encryption_key) b wg *
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._message_mac1_key) c wg *
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._secret_birthdate) bi wg *
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._secret_lock) lk wg *
  field_at sh t_dev (DOT FT._cookie_checker DOT FT._device) d wg * spacer sh 188 192 wg.
Proof.
  unfold_field_at (field_at _ _ (DOT FT._cookie_checker) _ _).
  apply pred_ext; cancel.
Qed.

Ltac hc4bt_dev_open FC4 :=
  rewrite (@field_at_change_composite Noise.CS CS4 _ _ t_dev (DOT FT._dev) _ _ (JMeq_refl _)) by reflexivity;
  rewrite (@field_at_change_composite Noise.CS CS4 _ _ t_dev (DOT FT._peer_hashtable) _ _ (JMeq_refl _)) by reflexivity;
  rewrite (@field_at_change_composite Noise.CS CS4 _ _ t_dev (DOT FT._index_hashtable) _ _ (JMeq_refl _)) by reflexivity;
  rewrite (hc4bt_dev_sid _ _ _ FC4), (hc4bt_dev_cc _ _ _ FC4);
  rewrite hc4bt_dev_split_sid, hc4bt_dev_split_cc;
  rewrite (field_at_data_at _ t_dev (DOT FT._static_identity DOT FT._static_public)),
    (field_at_data_at _ t_dev (DOT FT._static_identity DOT FT._static_private)),
    (field_at_data_at _ t_dev (DOT FT._cookie_checker DOT FT._secret)),
    (field_at_data_at _ t_dev (DOT FT._cookie_checker DOT FT._cookie_encryption_key)),
    (field_at_data_at _ t_dev (DOT FT._cookie_checker DOT FT._message_mac1_key));
  simpl nested_field_type.

Lemma hc4bt_dev_eq sh wg D :
  device_rep sh wg D =
  !! (@field_compatible Noise.CS t_dev [] wg /\ id_ok (d_id D) /\ cc_ok (d_cc D)) &&
  EX lk1: val, EX lk2: val, hc4bt_dvf sh wg D lk1 lk2.
Proof.
  unfold device_rep, identity_rep, checker_rep, hc4bt_dvf.
  apply pred_ext.
  - Intros lk1 lk2. Exists lk2 lk1.
    assert (FC4: field_compatible t_dev [] wg) by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_dev); auto).
    match goal with H: id_ok _ |- _ => destruct H as (I1 & I2) end.
    match goal with H: cc_ok _ |- _ => destruct H as (C1 & C2 & C3) end.
    hc4bt_dev_open FC4.
    rewrite !(hc4bt_hb sh _ 32) by assumption.
    entailer!; repeat split; auto.
  - Intros lk1 lk2.
    assert (FC4: field_compatible t_dev [] wg) by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_dev); auto).
    match goal with H: id_ok _ |- _ => destruct H as (I1 & I2) end.
    match goal with H: cc_ok _ |- _ => destruct H as (C1 & C2 & C3) end.
    Exists lk2 lk1.
    hc4bt_dev_open FC4.
    rewrite !(hc4bt_hb sh _ 32) by assumption.
    entailer!; repeat split; auto.
Qed.

(* the snapshot after dev_take *)
Definition hc4bt_dsf (sh: share) (s: val) (D: device) (h: val) : mpred :=
  field_at sh t_devsnap (DOT FT._dev) (d_dev D) s *
  data_at sh (tarray tuchar 32) (bytes (id_pub (d_id D))) (@field_address CKS t_devsnap (DOT FT._static_public) s) *
  data_at sh (tarray tuchar 32) (bytes (id_priv (d_id D))) (@field_address CKS t_devsnap (DOT FT._static_private) s) *
  field_at sh t_devsnap (DOT FT._has_identity) (Val.of_bool (id_has (d_id D))) s *
  data_at sh (tarray tuchar 32) (bytes (cc_secret (d_cc D))) (@field_address CKS t_devsnap (DOT FT._secret) s) * spacer sh 105 112 s *
  field_at sh t_devsnap (DOT FT._secret_birthdate) (Vlong (cc_birth (d_cc D))) s *
  data_at sh (tarray tuchar 32) (bytes (cc_ekey (d_cc D))) (@field_address CKS t_devsnap (DOT FT._cookie_encryption_key) s) *
  data_at sh (tarray tuchar 32) (bytes (cc_mkey (d_cc D))) (@field_address CKS t_devsnap (DOT FT._message_mac1_key) s) *
  field_at sh t_devsnap (DOT FT._checker_device) (cc_dev (d_cc D)) s *
  field_at sh t_devsnap (DOT FT._peer_hashtable) (d_ptab D) s *
  field_at sh t_devsnap (DOT FT._index_hashtable) (d_itab D) s *
  field_at sh t_devsnap (DOT FT._peers_head) h s.

Ltac hc4bt_dcc f := rewrite (@field_at_change_composite CKS CS4 _ _ t_devsnap (DOT f) _ _ (JMeq_refl _)) by reflexivity.
Ltac hc4bt_dar f := rewrite (@field_at_data_at CKS _ t_devsnap (DOT f)).

Lemma hc4bt_dev_snap_eq sh s D h : @data_at CKS sh t_devsnap (devsnap_val D h) s = hc4bt_dsf sh s D h.
Proof.
  unfold devsnap_val. unfold_data_at (@data_at CKS _ _ _ s).
  hc4bt_dar FT._static_public. hc4bt_dar FT._static_private. hc4bt_dar FT._secret.
  hc4bt_dar FT._cookie_encryption_key. hc4bt_dar FT._message_mac1_key.
  simpl nested_field_type.
  rewrite !(@WgNoise.proof.harness.common.hc3_body_ck.hc3b_ck_data_at_cs CKS CS4).
  hc4bt_dcc FT._dev. hc4bt_dcc FT._has_identity. hc4bt_dcc FT._secret_birthdate. hc4bt_dcc FT._checker_device.
  hc4bt_dcc FT._peer_hashtable. hc4bt_dcc FT._index_hashtable. hc4bt_dcc FT._peers_head.
  unfold hc4bt_dsf. apply pred_ext; cancel.
Qed.

(* the snapshot before dev_take (at CS4) *)
Lemma hc4bt_dev_snap_eq_ sh s :
  @data_at_ CS4 sh t_devsnap s =
  field_at_ sh t_devsnap (DOT FT._dev) s *
  hout sh 32 (field_address t_devsnap (DOT FT._static_public) s) *
  hout sh 32 (field_address t_devsnap (DOT FT._static_private) s) *
  field_at_ sh t_devsnap (DOT FT._has_identity) s *
  hout sh 32 (field_address t_devsnap (DOT FT._secret) s) * spacer sh 105 112 s *
  field_at_ sh t_devsnap (DOT FT._secret_birthdate) s *
  hout sh 32 (field_address t_devsnap (DOT FT._cookie_encryption_key) s) *
  hout sh 32 (field_address t_devsnap (DOT FT._message_mac1_key) s) *
  field_at_ sh t_devsnap (DOT FT._checker_device) s *
  field_at_ sh t_devsnap (DOT FT._peer_hashtable) s *
  field_at_ sh t_devsnap (DOT FT._index_hashtable) s *
  field_at_ sh t_devsnap (DOT FT._peers_head) s.
Proof.
  change (@data_at_ CS4 sh t_devsnap s) with (@data_at CS4 sh t_devsnap (Vundef, (Zrepeat Vundef 32,
    (Zrepeat Vundef 32, (Vundef, (Zrepeat Vundef 32, (Vundef, (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Vundef,
    (Vundef, (Vundef, Vundef))))))))))) s).
  unfold_data_at (data_at _ _ _ s).
  rewrite (field_at_data_at sh t_devsnap (DOT FT._static_public)), (field_at_data_at sh t_devsnap (DOT FT._static_private)),
    (field_at_data_at sh t_devsnap (DOT FT._secret)), (field_at_data_at sh t_devsnap (DOT FT._cookie_encryption_key)),
    (field_at_data_at sh t_devsnap (DOT FT._message_mac1_key)).
  unfold hout. rewrite !(@WgNoise.proof.harness.common.hc3_body_ck.hc3b_ck_data_at__cs HCS CS4).
  simpl nested_field_type. unfold data_at_, field_at_.
  apply pred_ext; cancel.
Qed.

Lemma hc4bt_dev_fa s f : @field_compatible CKS t_devsnap [] s ->
  In f [FT._static_public; FT._static_private; FT._secret; FT._cookie_encryption_key; FT._message_mac1_key] ->
  @field_address CKS t_devsnap (DOT f) s = @field_address CS4 t_devsnap (DOT f) s.
Proof.
  intros FC Hf. assert (FC4: @field_compatible CS4 t_devsnap [] s)
    by (apply (@field_compatible_change_composite CKS CS4 _ t_devsnap); auto).
  destruct Hf as [<- | [<- | [<- | [<- | [<- | []]]]]];
  rewrite (@field_address_offset CKS), (@field_address_offset CS4) by auto with field_compatible; reflexivity.
Qed.

Ltac hc4bt_dev_params :=
  match goal with |- context [Vlong (Int64.repr (Zlength ?A))] =>
    let E := fresh in assert (E: Zlength A = 32) by assumption; rewrite E end;
  simpl; rewrite !field_address_offset by auto with field_compatible;
  rewrite ?offset_offset_val; simpl; reflexivity.

Ltac hc4bt_fwd :=
  forward; try (entailer!; match goal with T: tc_val' _ ?v |- _ => apply T; solve [auto] end).

Lemma hc4bt_dev_take :
  @semax_body [] hc4_G_dev_take CS4 FT.f_dev_take dev_take4_spec.
Proof.
  start_function.
  rename H into HU.
  assert_PROP (@field_compatible CKS t_devsnap [] s) as FCs by entailer!.
  rewrite hc4bt_dev_eq. Intros lk1 lk2. unfold hc4bt_dvf.
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
  rewrite (@data_at__change_composite CKS CS4 _ shs t_devsnap) by reflexivity.
  rewrite hc4bt_dev_snap_eq_.
  inv HU. match goal with H: Forall _ _ |- _ => inv H end. match goal with H: Forall _ _ |- _ => inv H end.
  match goal with H: Forall _ _ |- _ => inv H end. match goal with H: Forall _ _ |- _ => inv H end.
  Intros.
  forward. { entailer!. match goal with T: tc_val' _ (d_dev D) |- _ => apply T; auto end. }
  forward.
  replace (hout shs 32 (field_address t_devsnap (DOT FT._static_public) s))
    with (hout shs (Zlength (id_pub (d_id D))) (field_address t_devsnap (DOT FT._static_public) s)) by (rewrite I1; reflexivity).
  forward_call (shs, field_address t_devsnap (DOT FT._static_public) s, shd,
                field_address t_dev (DOT FT._static_identity DOT FT._static_public) wg, id_pub (d_id D)).
  { entailer!. hc4bt_dev_params. }
  replace (hout shs 32 (field_address t_devsnap (DOT FT._static_private) s))
    with (hout shs (Zlength (id_priv (d_id D))) (field_address t_devsnap (DOT FT._static_private) s)) by (rewrite I2; reflexivity).
  forward_call (shs, field_address t_devsnap (DOT FT._static_private) s, shd,
                field_address t_dev (DOT FT._static_identity DOT FT._static_private) wg, id_priv (d_id D)).
  { entailer!. hc4bt_dev_params. }
  forward. { entailer!. destruct (id_has (d_id D)); hnf; auto. }
  forward.
  replace (hout shs 32 (field_address t_devsnap (DOT FT._secret) s))
    with (hout shs (Zlength (cc_secret (d_cc D))) (field_address t_devsnap (DOT FT._secret) s)) by (rewrite C1; reflexivity).
  forward_call (shs, field_address t_devsnap (DOT FT._secret) s, shd,
                field_address t_dev (DOT FT._cookie_checker DOT FT._secret) wg, cc_secret (d_cc D)).
  { entailer!. hc4bt_dev_params. }
  forward. forward.
  replace (hout shs 32 (field_address t_devsnap (DOT FT._cookie_encryption_key) s))
    with (hout shs (Zlength (cc_ekey (d_cc D))) (field_address t_devsnap (DOT FT._cookie_encryption_key) s)) by (rewrite C2; reflexivity).
  forward_call (shs, field_address t_devsnap (DOT FT._cookie_encryption_key) s, shd,
                field_address t_dev (DOT FT._cookie_checker DOT FT._cookie_encryption_key) wg, cc_ekey (d_cc D)).
  { entailer!. hc4bt_dev_params. }
  replace (hout shs 32 (field_address t_devsnap (DOT FT._message_mac1_key) s))
    with (hout shs (Zlength (cc_mkey (d_cc D))) (field_address t_devsnap (DOT FT._message_mac1_key) s)) by (rewrite C3; reflexivity).
  forward_call (shs, field_address t_devsnap (DOT FT._message_mac1_key) s, shd,
                field_address t_dev (DOT FT._cookie_checker DOT FT._message_mac1_key) wg, cc_mkey (d_cc D)).
  { entailer!. hc4bt_dev_params. }
  hc4bt_fwd.
  forward.
  hc4bt_fwd.
  forward.
  hc4bt_fwd.
  forward.
  forward.
  forward. { entailer!. match goal with H: value_fits t_ptab head |- _ => simplify_value_fits in H; apply H; auto end. }
  forward.
  rewrite hc4bt_dev_eq. Exists lk1 lk2. unfold hc4bt_dvf.
  unfold ptable. rewrite (@data_at_change_composite Noise.CS CS4 _ shp t_ptab _ _ (JMeq_refl _)) by reflexivity.
  rewrite hc4bt_dev_snap_eq. unfold hc4bt_dsf.
  rewrite !hc4bt_dev_fa by (auto; simpl; tauto).
  rewrite !(hc4bt_hb shs _ 32) by assumption.
  replace (force_val (sem_cast_i2bool (Val.of_bool (id_has (d_id D))))) with (Val.of_bool (id_has (d_id D)))
    by (destruct (id_has (d_id D)); reflexivity).
  entailer!.
  unfold id_ok, cc_ok; auto.
Qed.
End DEV.

(* ------------------------------------------------------------------------------------------------ *)
(* pr_take                                                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

Section PR.
#[local] Existing Instance CS4.
#[local] Instance hc4bt_pr_i1 : change_composite_env CKS CS4. make_cs_preserve CKS CS4. Defined.
#[local] Instance hc4bt_pr_i2 : change_composite_env CS4 CKS. make_cs_preserve CS4 CKS. Defined.
#[local] Instance hc4bt_pr_i3 : change_composite_env Noise.CS CS4. make_cs_preserve Noise.CS CS4. Defined.
#[local] Instance hc4bt_pr_i4 : change_composite_env CS4 Noise.CS. make_cs_preserve CS4 Noise.CS. Defined.

(* the fields of a peer that pr_take reads directly, at CS4 *)
Definition hc4bt_prf (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer (DOT FT._device) (p_device P) p *
  field_at sh t_peer (DOT FT._is_dead) (Val.of_bool (p_dead P)) p *
  (EX lk: val, field_at sh t_peer (DOT FT._keypairs) (p_cur P, (p_prev P, (p_next P, lk))) p) *
  field_at sh t_peer (DOT FT._last_sent_handshake) (Vlong (p_lsh P)) p *
  field_at sh t_peer (DOT FT._internal_id) (Vlong (p_id P)) p *
  field_at sh t_peer (DOT FT._pubkey_next) (p_pknext P) p.

(* the rest *)
Definition hc4bt_prr (sh: share) (p: val) (P: peer) : mpred :=
  !! (@field_compatible Noise.CS t_peer [] p) &&
  (hs_rep sh (hs_addr p) (p_hs P) * cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hc4bt_peer_eq sh p P : peer_rep sh p P = hc4bt_prf sh p P * hc4bt_prr sh p P.
Proof.
  unfold peer_rep, hc4bt_prf, hc4bt_prr, kps_rep.
  apply pred_ext.
  - Intros lk. Exists lk.
    assert (FC4: field_compatible t_peer [] p) by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_peer); auto).
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._device) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._is_dead) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._last_sent_handshake) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._internal_id) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._pubkey_next) _ _ (JMeq_refl _)) by reflexivity.
    rewrite (field_at_data_at sh t_peer (DOT FT._keypairs)).
    rewrite field_address_offset by auto with field_compatible.
    rewrite <- (@data_at_change_composite Noise.CS CS4 _ sh t_kps _ _ (JMeq_refl _)) by reflexivity.
    unfold kps_addr. simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros lk. Exists lk.
    assert (FC4: field_compatible t_peer [] p) by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_peer); auto).
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._device) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._is_dead) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._last_sent_handshake) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._internal_id) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FT._pubkey_next) _ _ (JMeq_refl _)) by reflexivity.
    rewrite (field_at_data_at sh t_peer (DOT FT._keypairs)).
    rewrite field_address_offset by auto with field_compatible.
    rewrite <- (@data_at_change_composite Noise.CS CS4 _ sh t_kps _ _ (JMeq_refl _)) by reflexivity.
    unfold kps_addr. simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.

Lemma hc4bt_lsh sh p (v: val) :
  field_at sh t_peer [StructField FT._last_sent_handshake] v p =
  field_at sh t_peer [StructField FT._counter; StructField FT._last_sent_handshake] v p.
Proof.
  rewrite (field_at_data_at sh t_peer [StructField FT._last_sent_handshake]).
  rewrite (field_at_data_at sh t_peer [StructField FT._counter; StructField FT._last_sent_handshake]).
  change [StructField FT._counter; StructField FT._last_sent_handshake]
    with ([StructField FT._counter] ++ [StructField FT._last_sent_handshake]).
  rewrite (field_address_app t_peer [StructField FT._last_sent_handshake] [StructField FT._counter]).
  simpl nested_field_type.
  unfold_data_at (data_at _ _ _ (field_address t_peer _ p)).
  rewrite field_at_data_at. reflexivity.
Qed.

(* the snapshot after pr_take *)
Definition hc4bt_snf (sh: share) (s: val) (P0: peer) : mpred :=
  field_at sh t_prsnap (DOT FT._device) (p_device P0) s *
  field_at sh t_prsnap (DOT FT._is_dead) (Val.of_bool (p_dead P0)) s * spacer sh 9 16 s *
  field_at sh t_prsnap (DOT FT._current_keypair) (p_cur P0) s *
  field_at sh t_prsnap (DOT FT._previous_keypair) (p_prev P0) s *
  field_at sh t_prsnap (DOT FT._next_keypair) (p_next P0) s *
  field_at sh t_prsnap (DOT FT._last_sent_handshake) (Vlong (p_lsh P0)) s *
  @data_at CKS sh t_cksnap (cksnap_val (p_cookie P0)) (@field_address CKS t_prsnap (DOT FT._cookie) s) *
  field_at sh t_prsnap (DOT FT._internal_id) (Vlong (p_id P0)) s *
  field_at sh t_prsnap (DOT FT._pubkey_next) (p_pknext P0) s.

Ltac hc4bt_cc f := rewrite (@field_at_change_composite CKS CS4 _ _ t_prsnap (DOT f) _ _ (JMeq_refl _)) by reflexivity.

Lemma hc4bt_snap_eq sh s P0 : @data_at CKS sh t_prsnap (prsnap_val P0) s = hc4bt_snf sh s P0.
Proof.
  unfold prsnap_val. unfold_data_at (@data_at CKS _ _ _ s).
  rewrite (@field_at_data_at CKS sh t_prsnap (DOT FT._cookie)).
  hc4bt_cc FT._device. hc4bt_cc FT._is_dead. hc4bt_cc FT._current_keypair. hc4bt_cc FT._previous_keypair.
  hc4bt_cc FT._next_keypair. hc4bt_cc FT._last_sent_handshake. hc4bt_cc FT._internal_id. hc4bt_cc FT._pubkey_next.
  unfold hc4bt_snf. apply pred_ext; cancel.
Qed.

(* the snapshot before pr_take (at CS4) *)
Lemma hc4bt_ck_def sh p :
  @data_at_ CKS sh t_cksnap p = @data_at CS4 sh t_cksnap (Vundef, (Vundef, (Zrepeat Vundef 16, (Vundef,
    (Zrepeat Vundef 16, (Zrepeat Vundef 32, Zrepeat Vundef 32)))))) p.
Proof.
  rewrite (@data_at__change_composite CKS CS4 _ sh t_cksnap) by reflexivity.
  reflexivity.
Qed.

Lemma hc4bt_snap_eq_ sh s :
  @data_at_ CS4 sh t_prsnap s =
  field_at_ sh t_prsnap (DOT FT._device) s *
  field_at_ sh t_prsnap (DOT FT._is_dead) s * spacer sh 9 16 s *
  field_at_ sh t_prsnap (DOT FT._current_keypair) s *
  field_at_ sh t_prsnap (DOT FT._previous_keypair) s *
  field_at_ sh t_prsnap (DOT FT._next_keypair) s *
  field_at_ sh t_prsnap (DOT FT._last_sent_handshake) s *
  @data_at_ CKS sh t_cksnap (field_address t_prsnap (DOT FT._cookie) s) *
  field_at_ sh t_prsnap (DOT FT._internal_id) s *
  field_at_ sh t_prsnap (DOT FT._pubkey_next) s.
Proof.
  change (@data_at_ CS4 sh t_prsnap s) with (@data_at CS4 sh t_prsnap (Vundef, (Vundef, (Vundef, (Vundef,
    (Vundef, (Vundef, ((Vundef, (Vundef, (Zrepeat Vundef 16, (Vundef, (Zrepeat Vundef 16, (Zrepeat Vundef 32,
     Zrepeat Vundef 32)))))), (Vundef, Vundef)))))))) s).
  unfold_data_at (data_at _ _ _ s).
  rewrite (field_at_data_at sh t_prsnap (DOT FT._cookie)).
  rewrite hc4bt_ck_def.
  simpl nested_field_type. unfold field_at_.
  apply pred_ext; cancel.
Qed.

Lemma hc4bt_pr_fa s : @field_compatible CKS t_prsnap [] s ->
  @field_address CKS t_prsnap (DOT FT._cookie) s = @field_address CS4 t_prsnap (DOT FT._cookie) s.
Proof.
  intros FC. assert (FC4: @field_compatible CS4 t_prsnap [] s)
    by (apply (@field_compatible_change_composite CKS CS4 _ t_prsnap); auto).
  rewrite (@field_address_offset CKS), (@field_address_offset CS4) by auto with field_compatible; reflexivity.
Qed.

Ltac hc4bt_fwd2 :=
  forward; try (entailer!; match goal with T: tc_val' _ ?v |- _ => apply T; solve [auto] end).

Lemma hc4bt_pr_take :
  @semax_body [] hc4_G_pr_take CS4 FT.f_pr_take pr_take4_spec.
Proof.
  start_function.
  rename H into HU.
  assert_PROP (@field_compatible CKS t_prsnap [] s) as FCs by entailer!.
  assert (FCs4: @field_compatible CS4 t_prsnap [] s)
    by (apply (@field_compatible_change_composite CKS CS4 _ t_prsnap); auto).
  assert (Ps: isptr s) by (destruct FCs; auto).
  rewrite hc4bt_peer_eq. unfold hc4bt_prf, hc4bt_prr. rewrite hc4bt_lsh. Intros lk.
  rewrite (@data_at__change_composite CKS CS4 _ shs t_prsnap) by reflexivity.
  rewrite hc4bt_snap_eq_.
  inv HU. match goal with H: Forall _ _ |- _ => inv H end. match goal with H: Forall _ _ |- _ => inv H end.
  match goal with H: Forall _ _ |- _ => inv H end. match goal with H: Forall _ _ |- _ => inv H end.
  match goal with H: Forall _ _ |- _ => inv H end.
  Intros.
  hc4bt_fwd2. forward. forward. { entailer!. destruct (p_dead P); hnf; auto. } forward.
  forward. { entailer!. match goal with H: value_fits _ (_, (_, (_, _))) |- _ =>
    simplify_value_fits in H; destruct H as (K1 & K2 & K3 & _) end. apply K1; auto. }
  forward.
  forward. { entailer!. match goal with H: value_fits _ (_, (_, (_, _))) |- _ =>
    simplify_value_fits in H; destruct H as (K1 & K2 & K3 & _) end. apply K2; auto. }
  forward.
  forward. { entailer!. match goal with H: value_fits _ (_, (_, (_, _))) |- _ =>
    simplify_value_fits in H; destruct H as (K1 & K2 & K3 & _) end. apply K3; auto. }
  forward. forward. forward.
  forward_call (shs, field_address t_prsnap (DOT FT._cookie) s, shp, cookie_addr p, p_cookie P).
  forward. forward. hc4bt_fwd2. forward.
  rewrite hc4bt_peer_eq. unfold hc4bt_prf, hc4bt_prr. rewrite hc4bt_lsh. Exists lk.
  rewrite hc4bt_snap_eq. unfold hc4bt_snf. rewrite hc4bt_pr_fa by assumption.
  replace (force_val (sem_cast_i2bool (Val.of_bool (p_dead P)))) with (Val.of_bool (p_dead P))
    by (destruct (p_dead P); reflexivity).
  entailer!.
Qed.
End PR.

Theorem hc4b_snap_take_ok :
  (@semax_body [] hc4_G_pr_take CS4 WgNoise.harness.x_cookie_mac.code.f_pr_take pr_take4_spec) /\
  (@semax_body [] hc4_G_dev_take CS4 WgNoise.harness.x_cookie_mac.code.f_dev_take dev_take4_spec) /\
  (@semax_body [] hc4_G_dev_take CS4skb WgNoise.harness.x_cookie_mac.code.f_skb_take skb_take4_spec).
Proof.
  split; [exact hc4bt_pr_take | split; [exact hc4bt_dev_take | exact hc4bt_skb_take]].
Qed.
