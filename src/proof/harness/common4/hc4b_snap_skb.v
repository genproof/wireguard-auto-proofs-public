
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
Require WgNoise.proof.harness.common.hc3_body_ck.
Local Open Scope logic.

Module FS := WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance CS4skb.
#[local] Instance hc4b_skb_i1 : change_composite_env CKS CS4skb. make_cs_preserve CKS CS4skb. Defined.
#[local] Instance hc4b_skb_i2 : change_composite_env Cookie.CS CS4skb. make_cs_preserve Cookie.CS CS4skb. Defined.

Lemma hc4b_skb_snap_split sh s (a l pr: val) (b4 b16 b2: list val) :
  @data_at CS4skb sh t_skbsnap (a, (l, (pr, (b4, (b16, b2))))) s =
  field_at sh t_skbsnap (DOT FS._data) a s * field_at sh t_skbsnap (DOT FS._len) l s *
  field_at sh t_skbsnap (DOT FS._protocol) pr s *
  data_at sh (tarray tuchar 4) b4 (field_address t_skbsnap (DOT FS._saddr4) s) *
  data_at sh (tarray tuchar 16) b16 (field_address t_skbsnap (DOT FS._saddr6) s) *
  data_at sh (tarray tuchar 2) b2 (field_address t_skbsnap (DOT FS._sport) s) *
  spacer sh 36 40 s.
Proof.
  unfold_data_at (data_at _ _ _ s).
  rewrite (field_at_data_at _ t_skbsnap (DOT FS._saddr4)), (field_at_data_at _ t_skbsnap (DOT FS._saddr6)),
    (field_at_data_at _ t_skbsnap (DOT FS._sport)).
  simpl nested_field_type. apply pred_ext; cancel.
Qed.

Lemma hc4b_skb_skb_split sh p (a l pr: val) (b4 b16 b2: list val) :
  @data_at CS4skb sh t_skb (a, (l, (pr, (b4, (b16, b2))))) p =
  field_at sh t_skb (DOT FS._data) a p * field_at sh t_skb (DOT FS._len) l p *
  field_at sh t_skb (DOT FS._protocol) pr p *
  data_at sh (tarray tuchar 4) b4 (field_address t_skb (DOT FS._ip4 DOT FS._saddr DOT FS._s_addr) p) *
  data_at sh (tarray tuchar 16) b16 (field_address t_skb (DOT FS._ip6 DOT FS._saddr DOT FS._s6_addr) p) *
  data_at sh (tarray tuchar 2) b2 (field_address t_skb (DOT FS._udp DOT FS._source) p) *
  spacer sh 36 40 p.
Proof.
  unfold_data_at (data_at _ _ _ p).
  unfold_field_at 4%nat. unfold_field_at 4%nat. unfold_field_at 5%nat. unfold_field_at 5%nat.
  unfold_field_at 6%nat.
  rewrite (field_at_data_at _ t_skb (DOT FS._ip4 DOT FS._saddr DOT FS._s_addr)),
    (field_at_data_at _ t_skb (DOT FS._ip6 DOT FS._saddr DOT FS._s6_addr)),
    (field_at_data_at _ t_skb (DOT FS._udp DOT FS._source)).
  simpl nested_field_type. apply pred_ext; cancel.
Qed.

Lemma hc4b_skb_hb {cs: compspecs} sh (bs: list byte) n p : Zlength bs = n ->
  @data_at cs sh (tarray tuchar n) (bytes bs) p = hbytes sh bs p.
Proof.
  intros <-. unfold hbytes. apply WgNoise.proof.harness.common.hc3_body_ck.hc3b_ck_data_at_cs.
Qed.

Lemma hc4b_skb_proto p0 p : 0 <= p0 <= 65535 -> 0 <= p <= 65535 ->
  Int.eq (Int.repr p0) (Int.repr p) = Z.eqb p0 p.
Proof.
  intros H0 H1. destruct (Z.eqb_spec p0 p) as [<- | Hne]; [apply Int.eq_true|].
  apply Int.eq_false. intros E. apply Hne.
  rewrite <- (Int.unsigned_repr p0), <- (Int.unsigned_repr p) by rep_lia. rewrite E. reflexivity.
Qed.

Lemma hc4b_skb_vp CSw VO x R : Forall vobj_ok VO -> (x = nullval \/ In x (hc4b_vobjs_vaddrs VO)) ->
  vobjs CSw VO * R |-- valid_pointer x.
Proof. intros HF Hx. apply (hc4b_vp_ok CSw VO []); auto; [simpl; tauto | intros []]. Qed.

Ltac hc4b_skb_vp_tac HVA CSw VO :=
  apply denote_tc_test_eq_split;
  (eapply derives_trans; [| apply (hc4b_skb_vp CSw VO _ TT); [assumption | apply HVA; simpl; tauto]]; cancel).

Ltac hc4b_skb_params :=
  simpl; rewrite ?field_address_offset by auto with field_compatible;
  rewrite ?offset_offset_val; simpl; try reflexivity.

Lemma hc4b_skb_same CSw
  (HV: forall VO x, In x (vobjs_addrs VO) -> In x (hc4b_vobjs_vaddrs VO)) :
  @semax_body [] hc4_G_dev_same CS4skb FS.f_skb_same (skb_same4_spec CSw).
Proof.
  start_function.
  match goal with H: Forall vobj_ok _ |- _ => rename H into HVO end.
  match goal with H: Forall (vp_ok _) _ |- _ => rename H into HPP end.
  match goal with H: skb_ok sk0 |- _ => destruct H as (HP0 & _ & _ & _) end.
  assert (HVA: forall x, In x [sk_data sk0; sk_data sk] -> x = nullval \/ In x (hc4b_vobjs_vaddrs VO)).
  { intros x Hx. rewrite Forall_forall in HPP. destruct (HPP x Hx) as [? | ?]; [left; auto | right; auto]. }
  unfold skb_rep. Intros.
  match goal with H: skb_ok sk |- _ => destruct H as (Pk & L4 & L6 & L2) end.
  rewrite (@data_at_change_composite CKS CS4skb _ shs t_skbsnap _ _ (JMeq_refl _)) by reflexivity.
  rewrite (@data_at_change_composite Cookie.CS CS4skb _ shk t_skb _ _ (JMeq_refl _)) by reflexivity.
  assert_PROP (@field_compatible CS4skb t_skbsnap [] s /\ @field_compatible CS4skb t_skb [] sp) as FC by entailer!.
  destruct FC as [FCs FCp].
  unfold skbsnap_val, skb_val.
  rewrite hc4b_skb_snap_split, hc4b_skb_skb_split.
  assert_PROP (Zlength (sk_ip4 sk0) = 4 /\ Zlength (sk_ip6 sk0) = 16 /\ Zlength (sk_port sk0) = 2) as JJ.
  { entailer!. unfold bytes in *. rewrite !Zlength_map in *. auto. }
  destruct JJ as (J4 & J6 & J2).
  rewrite !(hc4b_skb_hb shs _ 4) by assumption. rewrite !(hc4b_skb_hb shs _ 16) by assumption.
  rewrite !(hc4b_skb_hb shs _ 2) by assumption.
  rewrite !(hc4b_skb_hb shk _ 4) by assumption. rewrite !(hc4b_skb_hb shk _ 16) by assumption.
  rewrite !(hc4b_skb_hb shk _ 2) by assumption.
  assert_PROP (Forall is_pointer_or_null [sk_data sk0; sk_data sk]) as PN.
  { go_lowerx. apply hc4b_cmp_forall_prop. intros x Hx.
    eapply derives_trans; [| apply VST.floyd.VSU.valid_pointer_is_null_or_ptr].
    eapply derives_trans; [| apply (hc4b_skb_vp CSw VO x TT); [assumption | apply HVA; auto]].
    cancel. }
  rewrite Forall_forall in PN.
  assert (N1 := PN (sk_data sk0) ltac:(simpl; tauto)). assert (N2 := PN (sk_data sk) ltac:(simpl; tauto)).
  clear PN.
  assert_PROP (isptr s /\ isptr sp) as PP.
  { entailer!. split; match goal with H: field_compatible _ _ ?x |- isptr ?x => destruct H as [? _]; auto end. }
  destruct PP as [Ps Psp].
  Intros.
  forward. forward.
  forward_if (temp FS._t'1 (Val.of_bool (veqb (sk_data sk0) (sk_data sk) && Int.eq (sk_len sk0) (sk_len sk)))).
  { hc4b_skb_vp_tac HVA CSw VO. }
  { forward. forward. forward. entailer!. unfold veqb. rewrite if_true by auto. cbn [andb].
    unfold Int.cmpu. match goal with |- context [Int.eq ?a ?b] => destruct (Int.eq a b) end; reflexivity. }
  { forward. entailer!. unfold veqb. rewrite if_false by auto. reflexivity. }
  forward_if (temp FS._t'2 (Val.of_bool (veqb (sk_data sk0) (sk_data sk) && Int.eq (sk_len sk0) (sk_len sk) && Z.eqb (sk_proto sk0) (sk_proto sk)))).
  { forward. { entailer!. first [apply (proj2 HP0) | apply (proj2 Pk)]. }
    forward. { entailer!. first [apply (proj2 HP0) | apply (proj2 Pk)]. }
    forward. entailer!.
    match goal with H: typed_true tint _ |- _ => apply hc4b_cmp_tt in H; rewrite H end. cbn [andb].
    try rewrite hc4b_skb_proto by assumption.
    destruct (Z.eqb_spec (sk_proto sk0) (sk_proto sk)), (zeq (sk_proto sk0) (sk_proto sk)); try contradiction; reflexivity. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FS._t'3 (Val.of_bool (veqb (sk_data sk0) (sk_data sk) && Int.eq (sk_len sk0) (sk_len sk) && Z.eqb (sk_proto sk0) (sk_proto sk) && bytes_eqb (sk_ip4 sk0) (sk_ip4 sk)))).
  { forward_call (shs, @field_address CS4skb t_skbsnap (DOT FS._saddr4) s, sk_ip4 sk0, shk, @field_address CS4skb t_skb (DOT FS._ip4 DOT FS._saddr DOT FS._s_addr) sp, sk_ip4 sk).
    all: try (split; assumption).
    { entailer!. rewrite J4. hc4b_skb_params. }
    forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FS._t'5 (Val.of_bool (veqb (sk_data sk0) (sk_data sk) && Int.eq (sk_len sk0) (sk_len sk) && Z.eqb (sk_proto sk0) (sk_proto sk) && bytes_eqb (sk_ip4 sk0) (sk_ip4 sk) && bytes_eqb (sk_ip6 sk0) (sk_ip6 sk)))).
  { forward_call (shs, @field_address CS4skb t_skbsnap (DOT FS._saddr6) s, sk_ip6 sk0, shk, @field_address CS4skb t_skb (DOT FS._ip6 DOT FS._saddr DOT FS._s6_addr) sp, sk_ip6 sk).
    all: try (split; assumption).
    { entailer!. rewrite J6. hc4b_skb_params. }
    forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FS._t'7 (Val.of_bool (skb_eqb sk0 sk))).
  { forward_call (shs, @field_address CS4skb t_skbsnap (DOT FS._sport) s, sk_port sk0, shk, @field_address CS4skb t_skb (DOT FS._udp DOT FS._source) sp, sk_port sk).
    all: try (split; assumption).
    { entailer!. rewrite J2. hc4b_skb_params. }
    forward. entailer!.
    match goal with H: typed_true tint _ |- _ => apply hc4b_cmp_tt in H end.
    unfold skb_eqb. rewrite H. cbn [andb].
    match goal with |- context [bytes_eqb ?a ?b] => destruct (bytes_eqb a b) end; reflexivity. }
  { forward. entailer!.
    match goal with H: typed_false tint _ |- _ => apply hc4b_cmp_tf in H end.
    unfold skb_eqb. rewrite H. reflexivity. }
  forward.
  unfold skb_rep.
  rewrite (@data_at_change_composite CKS CS4skb _ shs t_skbsnap _ _ (JMeq_refl _)) by reflexivity.
  rewrite (@data_at_change_composite Cookie.CS CS4skb _ shk t_skb _ _ (JMeq_refl _)) by reflexivity.
  unfold skbsnap_val, skb_val.
  rewrite hc4b_skb_snap_split, hc4b_skb_skb_split.
  rewrite !(hc4b_skb_hb shs _ 4) by assumption. rewrite !(hc4b_skb_hb shs _ 16) by assumption.
  rewrite !(hc4b_skb_hb shs _ 2) by assumption.
  rewrite !(hc4b_skb_hb shk _ 4) by assumption. rewrite !(hc4b_skb_hb shk _ 16) by assumption.
  rewrite !(hc4b_skb_hb shk _ 2) by assumption.
  entailer!.
  split; [destruct (skb_eqb sk0 sk); reflexivity | unfold skb_ok; repeat split; auto; lia].
Qed.
