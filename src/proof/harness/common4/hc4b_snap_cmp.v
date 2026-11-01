(* (group snap of common4): the comparison bodies pr_same_but_cookie, pr_same. *)
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
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Module FC := WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance CS4.
#[local] Instance hc4b_cmp_i1 : change_composite_env CKS CS4. make_cs_preserve CKS CS4. Defined.
#[local] Instance hc4b_cmp_i2 : change_composite_env CS4 CKS. make_cs_preserve CS4 CKS. Defined.
#[local] Instance hc4b_cmp_i3 : change_composite_env Noise.CS CS4. make_cs_preserve Noise.CS CS4. Defined.
#[local] Instance hc4b_cmp_i4 : change_composite_env CS4 Noise.CS. make_cs_preserve CS4 Noise.CS. Defined.

Definition t_kps4 := Tstruct FC._noise_keypairs noattr.

(* the fields of a peer that pr_same_but_cookie reads, at CS4 *)
Definition hc4b_prf (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer (DOT FC._device) (p_device P) p *
  field_at sh t_peer (DOT FC._is_dead) (Val.of_bool (p_dead P)) p *
  (EX lk: val, field_at sh t_peer (DOT FC._keypairs) (p_cur P, (p_prev P, (p_next P, lk))) p) *
  field_at sh t_peer (DOT FC._last_sent_handshake) (Vlong (p_lsh P)) p *
  field_at sh t_peer (DOT FC._internal_id) (Vlong (p_id P)) p *
  field_at sh t_peer (DOT FC._pubkey_next) (p_pknext P) p.

(* the rest *)
Definition hc4b_prr (sh: share) (p: val) (P: peer) : mpred :=
  !! (@field_compatible Noise.CS t_peer [] p) &&
  (hs_rep sh (hs_addr p) (p_hs P) * cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hc4b_cmp_peer_eq sh p P : peer_rep sh p P = hc4b_prf sh p P * hc4b_prr sh p P.
Proof.
  unfold peer_rep, hc4b_prf, hc4b_prr, kps_rep.
  apply pred_ext.
  - Intros lk. Exists lk.
    assert (FC4: field_compatible t_peer [] p) by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_peer); auto).
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._device) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._is_dead) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._last_sent_handshake) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._internal_id) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._pubkey_next) _ _ (JMeq_refl _)) by reflexivity.
    rewrite (field_at_data_at sh t_peer (DOT FC._keypairs)).
    rewrite field_address_offset by auto with field_compatible.
    rewrite <- (@data_at_change_composite Noise.CS CS4 _ sh t_kps _ _ (JMeq_refl _)) by reflexivity.
    unfold kps_addr. simpl nested_field_type. simpl nested_field_offset.
    entailer!.
  - Intros lk. Exists lk.
    assert (FC4: field_compatible t_peer [] p) by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_peer); auto).
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._device) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._is_dead) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._last_sent_handshake) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._internal_id) _ _ (JMeq_refl _)) by reflexivity.
    rewrite <- (@field_at_change_composite Noise.CS CS4 _ sh t_peer (DOT FC._pubkey_next) _ _ (JMeq_refl _)) by reflexivity.
    rewrite (field_at_data_at sh t_peer (DOT FC._keypairs)).
    rewrite field_address_offset by auto with field_compatible.
    rewrite <- (@data_at_change_composite Noise.CS CS4 _ sh t_kps _ _ (JMeq_refl _)) by reflexivity.
    unfold kps_addr. simpl nested_field_type. simpl nested_field_offset.
    entailer!.
Qed.

Lemma hc4b_cmp_lsh sh p (v: val) :
  field_at sh t_peer [StructField FC._last_sent_handshake] v p =
  field_at sh t_peer [StructField FC._counter; StructField FC._last_sent_handshake] v p.
Proof.
  rewrite (field_at_data_at sh t_peer [StructField FC._last_sent_handshake]).
  rewrite (field_at_data_at sh t_peer [StructField FC._counter; StructField FC._last_sent_handshake]).
  change [StructField FC._counter; StructField FC._last_sent_handshake]
    with ([StructField FC._counter] ++ [StructField FC._last_sent_handshake]).
  rewrite (field_address_app t_peer [StructField FC._last_sent_handshake] [StructField FC._counter]).
  simpl nested_field_type.
  unfold_data_at (data_at _ _ _ (field_address t_peer _ p)).
  rewrite field_at_data_at. reflexivity.
Qed.

(* valid pointers *)
Lemma hc4b_cmp_vp CSw sh p (d: val) VO x R :
  readable_share sh -> Forall vobj_ok VO -> (x = nullval \/ x = p \/ In x (hc4b_vobjs_vaddrs VO)) ->
  @field_at CS4 sh t_peer (DOT FC._device) d p * vobjs CSw VO * R |-- valid_pointer x.
Proof.
  intros RS HF Hx. rewrite (sepcon_comm (field_at _ _ _ _ _)), sepcon_assoc.
  apply (hc4b_vp_ok CSw VO [p]); auto.
  - destruct Hx as [? | [-> | ?]]; simpl; tauto.
  - intros [<- | []]. apply sepcon_valid_pointer1.
    rewrite (@field_at_change_composite CS4 Noise.CS _ sh t_peer (DOT FC._device) _ _ (JMeq_refl _)) by reflexivity.
    apply (@field_at_valid_ptr0 Noise.CS); [auto | simpl; lia | reflexivity].
Qed.

(* a pointer comparison (both pointers or NULL) as veqb *)
Lemma hc4b_cmp_cmp x y : is_pointer_or_null x -> is_pointer_or_null y ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y))) = Val.of_bool (veqb x y).
Proof.
  intros Hx Hy. unfold veqb.
  destruct x; try contradiction; destruct y; try contradiction; simpl in Hx, Hy; subst;
  destruct (eq_dec _ _) as [Heq|Hne]; unfold sem_cmp_pp; simpl; try congruence; try reflexivity.
  - destruct (eq_block b b0); [|congruence]. subst. inv Heq. rewrite Ptrofs.eq_true. reflexivity.
  - destruct (eq_block b b0); [|reflexivity]. subst. rewrite Ptrofs.eq_false by congruence. reflexivity.
Qed.

Lemma hc4b_cmp_tt (b: bool) : typed_true tint (if b then Vtrue else Vfalse) -> b = true.
Proof. destruct b; auto. intros X. inv X. Qed.
Lemma hc4b_cmp_tf (b: bool) : typed_false tint (if b then Vtrue else Vfalse) -> b = false.
Proof. destruct b; auto. intros X. inv X. Qed.

Lemma hc4b_cmp_forall_prop (A: mpred) (Q: val -> Prop) (l: list val) :
  (forall x, In x l -> A |-- !! Q x) -> A |-- !! Forall Q l.
Proof.
  induction l as [|x l IH]; intros H.
  - apply prop_right; auto.
  - assert (H1: A |-- !! Q x) by (apply H; left; auto).
    assert (H2: A |-- !! Forall Q l) by (apply IH; intros; apply H; right; auto).
    apply derives_trans with (!! Q x && !! Forall Q l); [apply andp_right; auto|].
    normalize.
Qed.

Lemma hc4b_cmp_pn CSw sh p (d: val) VO x R :
  readable_share sh -> Forall vobj_ok VO -> (x = nullval \/ x = p \/ In x (hc4b_vobjs_vaddrs VO)) ->
  @field_at CS4 sh t_peer (DOT FC._device) d p * vobjs CSw VO * R |-- !! is_pointer_or_null x.
Proof.
  intros. eapply derives_trans; [apply hc4b_cmp_vp; eauto|]. apply VST.floyd.VSU.valid_pointer_is_null_or_ptr.
Qed.

Ltac hc4b_cmp_vp_tac HVA CSw sh p d VO :=
  apply denote_tc_test_eq_split;
  (eapply derives_trans; [| apply (hc4b_cmp_vp CSw sh p d VO _ TT); [assumption | assumption | apply HVA; simpl; tauto]];
   cancel).

Ltac hc4b_cmp_fin :=
  entailer!;
  match goal with H: typed_true tint _ |- _ => apply hc4b_cmp_tt in H; rewrite H end;
  cbn [andb];
  first [ rewrite hc4b_cmp_cmp by auto; reflexivity
        | match goal with |- Val.of_bool (Bool.eqb ?x ?y) = _ => destruct x, y; reflexivity end
        | (unfold Int64.cmp, Int64.cmpu;
           match goal with |- context [Int64.eq ?a ?b] => destruct (Int64.eq a b) end; reflexivity)
        | match goal with |- Val.of_bool ?X = _ => destruct X; reflexivity end ].
Ltac hc4b_cmp_fin_false :=
  entailer!;
  match goal with H: typed_false tint _ |- _ => apply hc4b_cmp_tf in H; rewrite H end;
  rewrite ?andb_false_l; reflexivity.

Definition hc4b_snf (sh: share) (s: val) (P0: peer) : mpred :=
  field_at sh t_prsnap (DOT FC._device) (p_device P0) s *
  field_at sh t_prsnap (DOT FC._is_dead) (Val.of_bool (p_dead P0)) s * spacer sh 9 16 s *
  field_at sh t_prsnap (DOT FC._current_keypair) (p_cur P0) s *
  field_at sh t_prsnap (DOT FC._previous_keypair) (p_prev P0) s *
  field_at sh t_prsnap (DOT FC._next_keypair) (p_next P0) s *
  field_at sh t_prsnap (DOT FC._last_sent_handshake) (Vlong (p_lsh P0)) s *
  @data_at CKS sh t_cksnap (cksnap_val (p_cookie P0)) (@field_address CKS t_prsnap (DOT FC._cookie) s) *
  field_at sh t_prsnap (DOT FC._internal_id) (Vlong (p_id P0)) s *
  field_at sh t_prsnap (DOT FC._pubkey_next) (p_pknext P0) s.

Ltac hc4b_cc f := rewrite (@field_at_change_composite CKS CS4 _ _ t_prsnap (DOT f) _ _ (JMeq_refl _)) by reflexivity.

Lemma hc4b_cmp_snap_eq sh s P0 : @data_at CKS sh t_prsnap (prsnap_val P0) s = hc4b_snf sh s P0.
Proof.
  unfold prsnap_val. unfold_data_at (@data_at CKS _ _ _ s).
  rewrite (@field_at_data_at CKS sh t_prsnap (DOT FC._cookie)).
  hc4b_cc FC._device. hc4b_cc FC._is_dead. hc4b_cc FC._current_keypair. hc4b_cc FC._previous_keypair.
  hc4b_cc FC._next_keypair. hc4b_cc FC._last_sent_handshake. hc4b_cc FC._internal_id. hc4b_cc FC._pubkey_next.
  unfold hc4b_snf. apply pred_ext; cancel.
Qed.

Lemma hc4b_cmp_pr_same_but_cookie CSw
  (HV: forall VO x, In x (vobjs_addrs VO) -> In x (hc4b_vobjs_vaddrs VO)) :
  @semax_body [] hc4_G_none CS4 FC.f_pr_same_but_cookie (pr_same_but_cookie4_spec CSw).
Proof.
  start_function.
  rename H into HVO. rename H0 into HPP. rename SH0 into RSp.
  assert (HVA: forall x, In x (pr_ptrs P0 P) -> x = nullval \/ x = p \/ In x (hc4b_vobjs_vaddrs VO)).
  { intros x Hx. rewrite Forall_forall in HPP. destruct (HPP x Hx) as [? | [? | ?]]; [left; auto | right; left; auto | right; right; auto]. }
  rewrite hc4b_cmp_peer_eq. unfold hc4b_prf. rewrite hc4b_cmp_lsh. Intros lk.
  rewrite hc4b_cmp_snap_eq. unfold hc4b_snf. Intros.
  assert_PROP (Forall is_pointer_or_null (pr_ptrs P0 P)) as PN.
  { go_lowerx. apply hc4b_cmp_forall_prop. intros x Hx.
    eapply derives_trans; [| apply (hc4b_cmp_pn CSw shp p (p_device P) VO x TT); auto].
    cancel. }
  unfold pr_ptrs in PN. rewrite Forall_forall in PN.
  assert (N1 := PN (p_device P0) ltac:(simpl; tauto)). assert (N2 := PN (p_device P) ltac:(simpl; tauto)).
  assert (N3 := PN (p_cur P0) ltac:(simpl; tauto)). assert (N4 := PN (p_cur P) ltac:(simpl; tauto)).
  assert (N5 := PN (p_prev P0) ltac:(simpl; tauto)). assert (N6 := PN (p_prev P) ltac:(simpl; tauto)).
  assert (N7 := PN (p_next P0) ltac:(simpl; tauto)). assert (N8 := PN (p_next P) ltac:(simpl; tauto)).
  assert (N9 := PN (p_pknext P0) ltac:(simpl; tauto)). assert (N10 := PN (p_pknext P) ltac:(simpl; tauto)).
  clear PN.
  forward. forward.
  forward_if (temp FC._t'1 (Val.of_bool (veqb (p_device P0) (p_device P) && Bool.eqb (p_dead P0) (p_dead P)))).
  { hc4b_cmp_vp_tac HVA CSw shp p (p_device P) VO. }
  { forward. { entailer!. destruct (p_dead P0); hnf; auto. }
    forward. { entailer!. destruct (p_dead P); hnf; auto. }
    forward. entailer!. unfold veqb. rewrite if_true by auto. cbn [andb].
    destruct (p_dead P0), (p_dead P); reflexivity. }
  { forward. entailer!. unfold veqb. rewrite if_false by auto. reflexivity. }
  forward_if (temp FC._t'2 (Val.of_bool (veqb (p_device P0) (p_device P) && Bool.eqb (p_dead P0) (p_dead P) && veqb (p_cur P0) (p_cur P)))).
  { forward. forward. forward. { entailer!. hc4b_cmp_vp_tac HVA CSw shp p (p_device P) VO. } hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FC._t'3 (Val.of_bool (veqb (p_device P0) (p_device P) && Bool.eqb (p_dead P0) (p_dead P) && veqb (p_cur P0) (p_cur P) && veqb (p_prev P0) (p_prev P)))).
  { forward. forward. forward. { entailer!. hc4b_cmp_vp_tac HVA CSw shp p (p_device P) VO. } hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FC._t'4 (Val.of_bool (veqb (p_device P0) (p_device P) && Bool.eqb (p_dead P0) (p_dead P) && veqb (p_cur P0) (p_cur P) && veqb (p_prev P0) (p_prev P) && veqb (p_next P0) (p_next P)))).
  { forward. forward. forward. { entailer!. hc4b_cmp_vp_tac HVA CSw shp p (p_device P) VO. } hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FC._t'5 (Val.of_bool (veqb (p_device P0) (p_device P) && Bool.eqb (p_dead P0) (p_dead P) && veqb (p_cur P0) (p_cur P) && veqb (p_prev P0) (p_prev P) && veqb (p_next P0) (p_next P) && Int64.eq (p_lsh P0) (p_lsh P)))).
  { forward. forward. forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FC._t'6 (Val.of_bool (veqb (p_device P0) (p_device P) && Bool.eqb (p_dead P0) (p_dead P) && veqb (p_cur P0) (p_cur P) && veqb (p_prev P0) (p_prev P) && veqb (p_next P0) (p_next P) && Int64.eq (p_lsh P0) (p_lsh P) && Int64.eq (p_id P0) (p_id P)))).
  { forward. forward. forward. hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward_if (temp FC._t'7 (Val.of_bool (veqb (p_device P0) (p_device P) && Bool.eqb (p_dead P0) (p_dead P) && veqb (p_cur P0) (p_cur P) && veqb (p_prev P0) (p_prev P) && veqb (p_next P0) (p_next P) && Int64.eq (p_lsh P0) (p_lsh P) && Int64.eq (p_id P0) (p_id P) && veqb (p_pknext P0) (p_pknext P)))).
  { forward. forward. forward. { entailer!. hc4b_cmp_vp_tac HVA CSw shp p (p_device P) VO. } hc4b_cmp_fin. }
  { forward. hc4b_cmp_fin_false. }
  forward.
  rewrite hc4b_cmp_peer_eq. unfold hc4b_prf. rewrite hc4b_cmp_lsh. Exists lk.
  rewrite hc4b_cmp_snap_eq. unfold hc4b_snf. entailer!.
  unfold pr_eqb_nc. match goal with |- Val.of_bool ?X = _ => destruct X; reflexivity end.
Qed.

Lemma hc4b_cmp_pr_same CSw :
  @semax_body [] (hc4_G_pr_same CSw) CS4 FC.f_pr_same (pr_same4_spec CSw).
Proof.
  start_function.
  forward_call (shs, s, P0, shp, p, P, VO).
  forward_if (temp FC._t'2 (Val.of_bool (pr_eqb P0 P))).
  { assert_PROP (@field_compatible CKS t_prsnap [] s) as FCs by entailer!.
    rewrite hc4b_cmp_peer_eq. unfold hc4b_prr. Intros.
    rewrite hc4b_cmp_snap_eq. unfold hc4b_snf. Intros.
    forward_call (shs, @field_address CKS t_prsnap (DOT FC._cookie) s, p_cookie P0, shp, cookie_addr p, p_cookie P).
    { split; [destruct FCs | match goal with H: field_compatible t_peer [] p |- _ => destruct H end]; auto. }
    forward. entailer!.
    + unfold pr_eqb. destruct (pr_eqb_nc P0 P); [| exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end].
      destruct (cookie_eqb _ _); reflexivity.
    + rewrite hc4b_cmp_peer_eq. unfold hc4b_prr. rewrite hc4b_cmp_snap_eq. unfold hc4b_snf.
      entailer!. }
  { forward. entailer!. unfold pr_eqb. destruct (pr_eqb_nc P0 P); [discriminate | reflexivity]. }
  forward. apply prop_right. destruct (pr_eqb P0 P); reflexivity.
Qed.
