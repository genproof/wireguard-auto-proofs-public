(* nb port of the hc4b_ke_add_segD.v., (kents_add): segment D of the loop body, the slot fill. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_add_defs.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Section SegD.
#[local] Existing Instance CS4nb.

#[local] Instance hc4nb2_ke_aD_cce : change_composite_env Noise.CS CS4nb.
Proof. make_cs_preserve Noise.CS CS4nb. Defined.

(* the peer without its keypair slots *)
Definition hc4nb2_ke_aD_rest (sh: share) (p: val) (P: peer) : mpred :=
  @field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
  @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  hs_rep sh (hs_addr p) (p_hs P) *
  @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
  @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma hc4nb2_ke_aD_kps sh p v :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_kps v (kps_addr p) = @field_at CS4nb sh t_peer (DOT HC._keypairs) v p.
Proof.
  intros FC.
  assert (CP: cs_preserve_type Noise.CS CS4nb (coeq Noise.CS CS4nb) t_peer = true) by (vm_compute; reflexivity).
  rewrite <- (@field_at_change_composite Noise.CS CS4nb _ sh t_peer (DOT HC._keypairs) v v (JMeq_refl v) CP).
  rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc4nb2_ke_aD_split sh p P cur prev next :
  peer_rep sh p (p_set_slots P cur prev next) =
  !! @field_compatible Noise.CS t_peer [] p &&
  (hc4nb2_ke_aD_rest sh p P * EX lk: val, @field_at CS4nb sh t_peer (DOT HC._keypairs) (cur, (prev, (next, lk))) p).
Proof.
  unfold peer_rep, hc4nb2_ke_aD_rest, kps_rep. simpl.
  apply pred_ext; Intros; [| Intros lk]; apply andp_right; try (apply prop_right; auto).
  - Intros lk. Exists lk. rewrite hc4nb2_ke_aD_kps by auto. cancel.
  - Exists lk. rewrite hc4nb2_ke_aD_kps by auto. cancel.
Qed.

Lemma hc4nb2_ke_aD_set_id P : p_set_slots P (p_cur P) (p_prev P) (p_next P) = P.
Proof. destruct P; reflexivity. Qed.

Lemma hc4nb2_ke_aD_fill_notin (l: list (val * share * peer)) d :
  ~ In (kd_owner d) (map peer_addr4 l) -> fill_peers l d = l.
Proof.
  intros H. unfold fill_peers. rewrite <- (map_id l) at 2. apply map_ext_in.
  intros [[a sh] P] Hin. destruct (eq_dec a (kd_owner d)); auto.
  subst. exfalso. apply H. apply in_map_iff. exists (kd_owner d, sh, P). auto.
Qed.

Lemma hc4nb2_ke_aD_fold PS l1 l2 owner sh P d :
  PS = l1 ++ (owner, sh, P) :: l2 -> NoDup (map peer_addr4 PS) -> kd_owner d = owner ->
  peer_rep sh owner (fill_slot P (kd_addr d) (kd_slot d)) * peers_rep (l1 ++ l2) |-- peers_rep (fill_peers PS d).
Proof.
  intros -> ND Ho.
  rewrite map_app in ND. simpl in ND. apply NoDup_remove_2 in ND.
  rewrite in_app_iff in ND.
  assert (E: fill_peers (l1 ++ (owner, sh, P) :: l2) d =
             fill_peers l1 d ++ (owner, sh, fill_slot P (kd_addr d) (kd_slot d)) :: fill_peers l2 d).
  { unfold fill_peers. rewrite map_app. simpl. rewrite if_true by auto. reflexivity. }
  rewrite E, !hc4nb2_ke_aD_fill_notin by (rewrite Ho; tauto).
  unfold peers_rep. rewrite !iter_sepcon_app. simpl. cancel.
Qed.

Lemma hc4nb2_ke_aD_unfold PS l1 l2 owner sh P :
  PS = l1 ++ (owner, sh, P) :: l2 -> peers_rep PS = peer_rep sh owner P * peers_rep (l1 ++ l2).
Proof.
  intros ->. unfold peers_rep. rewrite !iter_sepcon_app. simpl. apply pred_ext; cancel.
Qed.

(* if (fill) switch (nondet_u8() % 4) { case c: if (owner->keypairs.<slot c> == NULL) <slot c> = kp; } :
   the model fill_peers (hc4_model.v) with the drawn c (any c in 0..3 when fill = 0: kents_PS ignores it) *)
Lemma hc4nb2_ke_aD_split0 sh p P :
  peer_rep sh p P =
  !! @field_compatible Noise.CS t_peer [] p &&
  (hc4nb2_ke_aD_rest sh p P * EX lk: val, @field_at CS4nb sh t_peer (DOT HC._keypairs) (p_cur P, (p_prev P, (p_next P, lk))) p).
Proof.
  rewrite <- hc4nb2_ke_aD_split. rewrite hc4nb2_ke_aD_set_id. reflexivity.
Qed.

Lemma hc4nb2_ke_aD_back sh p P cur prev next lk :
  @field_compatible Noise.CS t_peer [] p ->
  hc4nb2_ke_aD_rest sh p P * @field_at CS4nb sh t_peer (DOT HC._keypairs) (cur, (prev, (next, lk))) p |--
  peer_rep sh p (p_set_slots P cur prev next).
Proof.
  intros FC. rewrite hc4nb2_ke_aD_split. apply andp_right; [apply prop_right; auto|]. Exists lk. cancel.
Qed.

Lemma hc4nb2_ke_aD_saddrs_in (D: list (val * share * entry)) a :
  In a (saddrs D) -> exists sh E, In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct H as [<- | H]; [eauto|]. destruct (IH H) as (sh & E & HI). eauto.
Qed.

(* a pool address is a valid pointer (the pool entry owns it) *)
Lemma hc4nb2_ke_aD_vp_itab sh tab T x R :
  readable_share sh -> In x (saddrs (t_D T)) -> itable sh tab T * R |-- valid_pointer x.
Proof.
  intros RS Hin.
  apply sepcon_valid_pointer1. unfold itable. Intros. apply sepcon_valid_pointer2.
  destruct (hc4nb2_ke_aD_saddrs_in _ _ Hin) as (shx & E & HE).
  eapply derives_trans; [apply iter_sepcon_in_true; exact HE|].
  apply sepcon_valid_pointer1. unfold pool_item_rep, entry_at.
  assert (writable_share shx).
  { destruct H as (_ & _ & _ & HF). rewrite Forall_forall in HF. apply (HF _ HE). }
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4nb2_ke_aD_vp sh tab T x R :
  readable_share sh -> vp_ok (saddrs (t_D T)) x -> itable sh tab T * R |-- valid_pointer x.
Proof.
  intros RS [-> | Hin]; [apply valid_pointer_null | apply hc4nb2_ke_aD_vp_itab; auto].
Qed.

Lemma hc4nb2_ke_aD_pn sh tab T x R :
  readable_share sh -> vp_ok (saddrs (t_D T)) x -> itable sh tab T * R |-- !! is_pointer_or_null x.
Proof.
  intros RS V. eapply derives_trans; [apply hc4nb2_ke_aD_vp; eauto | apply VSU.valid_pointer_is_null_or_ptr].
Qed.

Lemma hc4nb2_ke_aD_fill_set P k c :
  p_set_slots P (p_cur (fill_slot P k c)) (p_prev (fill_slot P k c)) (p_next (fill_slot P k c)) = fill_slot P k c.
Proof.
  unfold fill_slot. repeat (destruct (Z.eq_dec _ _) || destruct (eq_dec _ _)); destruct P; reflexivity.
Qed.

Lemma hc4nb2_ke_aD_close PS l1 l2 owner sh P k K idx c (lk: val) :
  PS = l1 ++ (owner, sh, P) :: l2 -> NoDup (map peer_addr4 PS) -> @field_compatible Noise.CS t_peer [] owner ->
  hc4nb2_ke_aD_rest sh owner P *
  @field_at CS4nb sh t_peer (DOT HC._keypairs)
    (p_cur (fill_slot P k c), (p_prev (fill_slot P k c), (p_next (fill_slot P k c), lk))) owner *
  peers_rep (l1 ++ l2) |-- peers_rep (fill_peers PS (mkKD k owner K idx c)).
Proof.
  intros EPS ND FC.
  sep_apply (hc4nb2_ke_aD_back sh owner P (p_cur (fill_slot P k c)) (p_prev (fill_slot P k c)) (p_next (fill_slot P k c)) lk FC).
  rewrite hc4nb2_ke_aD_fill_set.
  apply (hc4nb2_ke_aD_fold PS l1 l2 owner sh P (mkKD k owner K idx c) EPS ND eq_refl).
Qed.

Lemma hc4nb2_ke_add_segD_ok {Espec: OracleKind} (CSw: hc4nb2_ke_add_csw) (l k n i owner tab peers p: val) (fl: int)
    (gv: globals) (sht: share) (T: tstate) (PS: list (val * share * peer)) (K: keypair) (idx: int) (FR: mpred) :
  readable_share sht -> peers_wf PS -> NoDup (map peer_addr4 PS) -> In owner (map peer_addr4 PS) ->
  In k (saddrs (t_D T)) -> hc4nb2_ke_add_slots_ok (saddrs (t_D T)) PS ->
  @semax CS4nb Espec (hc4nb2_ke_add_Delta CSw)
    (PROPx [] (LOCALx (hc4nb2_ke_add_locs l k n i owner tab peers p fl gv)
      (SEPx [peers_rep PS; itable sht tab T; FR])))
    hc4nb2_ke_add_sD
    (normal_ret_assert (EX c: Z,
      PROPx [0 <= c <= 3] (LOCALx (hc4nb2_ke_add_locs l k n i owner tab peers p fl gv)
        (SEPx [peers_rep (if negb (Int.eq fl Int.zero) then fill_peers PS (mkKD k owner K idx c) else PS);
               itable sht tab T; FR])))).
Proof.
  intros RS W ND Hin Hk SL.
  apply in_map_iff in Hin. destruct Hin as [[[o sh] P] [Eo HinP]]. simpl in Eo. subst o.
  destruct (in_split _ _ HinP) as (l1 & l2 & EPS).
  assert (Wsh: writable_share sh) by (unfold peers_wf in W; rewrite Forall_forall in W; exact (W _ HinP)).
  assert (SLP: Forall (vp_ok (saddrs (t_D T))) [p_cur P; p_prev P; p_next P])
    by (unfold hc4nb2_ke_add_slots_ok in SL; rewrite Forall_forall in SL; exact (SL _ HinP)).
  rewrite (hc4nb2_ke_aD_unfold PS l1 l2 owner sh P EPS).
  rewrite (hc4nb2_ke_aD_split0 sh owner P).
  Intros lk.
  unfold hc4nb2_ke_add_sD, hc4nb2_ke_add_locs. unfold hc4nb2_ke_add_Delta. abbreviate_semax.
  forward_if.
  2: {
    forward. Exists 0. entailer!. rewrite Int.eq_true. simpl negb.
    match goal with |- _ |-- peers_rep (if false then _ else ?X) => change (peers_rep (if false then _ else X)) with (peers_rep X) end.
    rewrite (hc4nb2_ke_aD_unfold _ l1 l2 owner sh P eq_refl).
    sep_apply (hc4nb2_ke_aD_back sh owner P (p_cur P) (p_prev P) (p_next P) lk H).
    rewrite hc4nb2_ke_aD_set_id. cancel. }
  inversion SLP as [|? ? V1 SLP1]; inversion SLP1 as [|? ? V2 SLP2]; inversion SLP2 as [|? ? V3 _]. subst.
  assert_PROP (is_pointer_or_null (p_cur P) /\ is_pointer_or_null (p_prev P) /\ is_pointer_or_null (p_next P)) as PN.
  {
    go_lowerx. apply derives_trans with (itable sht tab T * TT); [cancel|].
    apply derives_trans with (!! is_pointer_or_null (p_cur P) && !! is_pointer_or_null (p_prev P) &&
                              !! is_pointer_or_null (p_next P)).
    - repeat apply andp_right; apply hc4nb2_ke_aD_pn; auto.
    - rewrite <- !prop_and. apply prop_derives. tauto. }
  forward_call tt. Intros b.
  apply (semax_switch_PQR (b mod 4)); [reflexivity | entailer! | entailer! | ].
  { destruct H7 as [_ E]; discriminate. }
  { f_equal. unfold Int.mods. rewrite !Int.signed_repr by rep_lia. rewrite Z.rem_mod_nonneg by lia. reflexivity. }
  rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 4); rep_lia).
  assert (b mod 4 = 0 \/ b mod 4 = 1 \/ b mod 4 = 2 \/ b mod 4 = 3) as [E|[E|[E|E]]]
    by (pose proof (Z.mod_pos_bound b 4); lia);
    rewrite E; match goal with |- semax _ _ ?c _ => let c' := eval simpl in c in change c with c' end.
  - forward.
    { entailer!. tauto. }
    forward_if (PROP () LOCAL (temp HC._l l; temp HC._k k; temp HC._n n; temp HC._i i; temp HC._owner owner;
        temp HC._kp k; gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl))
      SEP (hc4nb2_ke_aD_rest sh owner P;
           field_at sh t_peer (DOT HC._keypairs)
             (p_cur (fill_slot P k 0), (p_prev (fill_slot P k 0), (p_next (fill_slot P k 0), lk))) owner;
           peers_rep (l1 ++ l2); itable sht tab T; FR)).
    { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
      apply derives_trans with (itable sht tab T * TT); [cancel | apply hc4nb2_ke_aD_vp; auto]. }
    { forward. entailer!. unfold fill_slot. simpl. rewrite H2. simpl. apply derives_refl. }
    { forward. entailer!. unfold fill_slot. simpl. rewrite if_false by auto. apply derives_refl. }
    forward. Exists 0. entailer!. rewrite Int.eq_false by auto. simpl negb.
    apply (hc4nb2_ke_aD_close _ l1 l2 owner sh P k K idx 0 lk eq_refl ND H).
  - forward.
    { entailer!. tauto. }
    forward_if (PROP () LOCAL (temp HC._l l; temp HC._k k; temp HC._n n; temp HC._i i; temp HC._owner owner;
        temp HC._kp k; gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl))
      SEP (hc4nb2_ke_aD_rest sh owner P;
           field_at sh t_peer (DOT HC._keypairs)
             (p_cur (fill_slot P k 1), (p_prev (fill_slot P k 1), (p_next (fill_slot P k 1), lk))) owner;
           peers_rep (l1 ++ l2); itable sht tab T; FR)).
    { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
      apply derives_trans with (itable sht tab T * TT); [cancel | apply hc4nb2_ke_aD_vp; auto]. }
    { forward. entailer!. unfold fill_slot. simpl. rewrite H2. simpl. apply derives_refl. }
    { forward. entailer!. unfold fill_slot. simpl. rewrite if_false by auto. apply derives_refl. }
    forward. Exists 1. entailer!. rewrite Int.eq_false by auto. simpl negb.
    apply (hc4nb2_ke_aD_close _ l1 l2 owner sh P k K idx 1 lk eq_refl ND H).
  - forward.
    { entailer!. tauto. }
    forward_if (PROP () LOCAL (temp HC._l l; temp HC._k k; temp HC._n n; temp HC._i i; temp HC._owner owner;
        temp HC._kp k; gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl))
      SEP (hc4nb2_ke_aD_rest sh owner P;
           field_at sh t_peer (DOT HC._keypairs)
             (p_cur (fill_slot P k 2), (p_prev (fill_slot P k 2), (p_next (fill_slot P k 2), lk))) owner;
           peers_rep (l1 ++ l2); itable sht tab T; FR)).
    { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
      apply derives_trans with (itable sht tab T * TT); [cancel | apply hc4nb2_ke_aD_vp; auto]. }
    { forward. entailer!. unfold fill_slot. simpl. rewrite H2. simpl. apply derives_refl. }
    { forward. entailer!. unfold fill_slot. simpl. rewrite if_false by auto. apply derives_refl. }
    forward. Exists 2. entailer!. rewrite Int.eq_false by auto. simpl negb.
    apply (hc4nb2_ke_aD_close _ l1 l2 owner sh P k K idx 2 lk eq_refl ND H).
  - forward. Exists 3. entailer!. rewrite Int.eq_false by auto. simpl negb.
    apply (hc4nb2_ke_aD_close _ l1 l2 owner sh P k K idx 3 lk eq_refl ND H).
Qed.
End SegD.
