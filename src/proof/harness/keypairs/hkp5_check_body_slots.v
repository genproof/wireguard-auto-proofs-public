(* law keypairs: the segment SLOTS (P's three slots).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.
Require Import WgNoise.proof.protocol.prot3_noise_rot_lemmas.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

#[local] Instance hkc5s_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkc5s_afind_ex {A: Type} (l: list (val * A)) a :
  In a (map fst l) -> exists v, afind l a = Some v.
Proof.
  induction l as [|[x w] l IH]; simpl; intros Hi; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct Hi; [congruence|auto].
Qed.

Lemma hkc5s_afind_In {A: Type} (l: list (val * A)) a v :
  afind l a = Some v -> In (a, v) l.
Proof.
  induction l as [|[x w] l IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; auto|auto].
Qed.

Lemma hkc5s_f2 p T (ML: list (val * hk5_mk)) (KS: list (val * keypair)) m M :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  In (m, M) ML -> exists K, hk5_match p T M K.
Proof.
  intros HF. induction HF as [|x y ML' KS' [_ Hxy] _ IH]; simpl; intros Hi; [contradiction|].
  destruct Hi as [Hx|Hi]; [subst x; eauto | auto].
Qed.

(* a slot: NULL, or a live node whose keypair is an Ews entry of the table's pool *)
Lemma hkc5s_slot p OD OH H P KS T s :
  hk5_rel p OD OH H P KS T -> In s (hk5_slots H) ->
  (s = nullval /\ hk5_slot_kp (h5_ML H) s = nullval) \/
  (exists M E, In (s, M) (h5_ML H) /\ hk5_slot_kp (h5_ML H) s = m5_kp M /\
             sfind (t_D T) (m5_kp M) = Some (Ews, E) /\ s <> nullval).
Proof.
  intros ((HF & _ & Hnn & _ & _ & Hsl & _) & _) Hin.
  rewrite Forall_forall in Hsl. destruct (Hsl s Hin) as [-> | Hi].
  - left. split; [reflexivity|]. unfold hk5_slot_kp. rewrite if_true by reflexivity. reflexivity.
  - right. destruct (hkc5s_afind_ex _ _ Hi) as [M HM].
    assert (Hs: s <> nullval) by (intros ->; contradiction).
    assert (HIn := hkc5s_afind_In _ _ _ HM).
    destruct (hkc5s_f2 _ _ _ _ _ _ HF HIn) as (K & _ & Hsf & _).
    exists M, (mkEntry p IDX_KEYPAIR (m5_index M)).
    split; [auto|]. split; [|auto].
    unfold hk5_slot_kp. rewrite if_false by auto. rewrite HM. reflexivity.
Qed.

Local Open Scope logic.

Lemma hkc5s_focus ML m M : In (m, M) ML ->
  exists nx Rest, hk5_mklist ML = hk5_node m M nx * Rest.
Proof.
  induction ML as [|[x X] ML IH]; simpl; intros Hi; [contradiction|].
  destruct Hi as [Hx|Hi].
  - inv Hx. eauto.
  - destruct (IH Hi) as (nx & Rest & ->). exists nx, (hk5_node x X (hk5_head ML) * Rest).
    rewrite <- !sepcon_assoc, (sepcon_comm (hk5_node x X _)). reflexivity.
Qed.

Lemma hkc5s_mkvalid ML m M : In (m, M) ML -> hk5_mklist ML |-- valid_pointer m.
Proof.
  intros Hi. destruct (hkc5s_focus _ _ _ Hi) as (nx & Rest & ->).
  apply sepcon_valid_pointer1. unfold hk5_node.
  apply andp_left2. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable, writable_Ews | reflexivity].
Qed.

Lemma hkc5s_mk_pn ML m M : In (m, M) ML -> hk5_mklist ML |-- !! is_pointer_or_null m.
Proof.
  intros Hi. eapply derives_trans; [eapply hkc5s_mkvalid; eauto |].
  constructor; apply valid_pointer_is_pointer_or_null.
Qed.

Lemma hkc5s_pool_pn sht t T a E : sfind (t_D T) a = Some (Ews, E) -> itable sht t T |-- !! is_pointer_or_null a.
Proof.
  intros Hi. eapply derives_trans; [eapply prot3_noise_rot_pool_valid; eauto |].
  constructor; apply valid_pointer_is_pointer_or_null.
Qed.

Lemma hkc5s_cmp_self v : is_pointer_or_null v -> force_val (sem_cmp_pp Cne v v) = Vint Int.zero.
Proof.
  destruct v; simpl; intros Hv; try contradiction.
  - subst. reflexivity.
  - unfold sem_cmp_pp; simpl. rewrite if_true by auto. rewrite Ptrofs.eq_true. reflexivity.
Qed.

(* the peer's keypairs struct as a field of the peer, at W_keypairs *)
Lemma hkc5s_kps_eq sh p (a b c d: val) :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_kps (a, (b, (c, d))) (kps_addr p) =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._keypairs] (a, (b, (c, d))) p.
Proof.
  intros FC. rewrite prot3_noise_rot_kps_field by auto.
  assert (Hc: cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkc5s_CCE) t_peer = true)
    by (vm_compute; reflexivity).
  exact (f_equal (fun f => f p) (@field_at_change_composite Noise.CS W_keypairs hkc5s_CCE sh t_peer
           [StructField prot_repr3.I._keypairs] (a, (b, (c, d))) (a, (b, (c, d))) (JMeq_refl _) Hc)).
Qed.

Definition hkc5s_kps (sh: share) (p: val) (P: peer) : mpred :=
  EX lk: val, @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._keypairs]
                (p_cur P, (p_prev P, (p_next P, lk))) p.

Lemma hkc5s_peer sh p P :
  peer_rep sh p P = hkc5s_kps sh p P * prot3_noise_rot_peer_rest sh p P.
Proof.
  rewrite prot3_noise_rot_peer_split. unfold prot3_noise_rot_peer_rest, kps_rep, hkc5s_kps.
  apply pred_ext.
  - Intros lk. Exists lk. rewrite hkc5s_kps_eq by auto. entailer!.
  - Intros lk. Exists lk. rewrite hkc5s_kps_eq by auto. entailer!.
Qed.

Lemma hkc5_slots_ok : hkc5_slots_stmt.
Proof.
  intros Espec x25519 F V Y O R.
  unfold hkc5_S. Intros.
  pose proof H0 as (Hrel & _).
  pose proof Hrel as (_ & _ & Hprev & Hcur & Hnext).
  assert (Sp := hkc5s_slot _ _ _ _ _ _ _ (h5_sp (y_H Y)) Hrel ltac:(unfold hk5_slots; simpl; auto)).
  assert (Sc := hkc5s_slot _ _ _ _ _ _ _ (h5_sc (y_H Y)) Hrel ltac:(unfold hk5_slots; simpl; auto)).
  assert (Sn := hkc5s_slot _ _ _ _ _ _ _ (h5_sn (y_H Y)) Hrel ltac:(unfold hk5_slots; simpl; auto)).
  clear Hrel.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkc5_slots, hkc5_lv. cbn [app].
  rewrite hkc5s_peer. unfold hkc5s_kps. Intros lk.
  destruct R as [Rn Rb Rc Rr].
  abbreviate_semax.
  set (HH := y_H Y) in *. set (PP := y_P Y) in *. set (TT := y_T Y) in *.
  assert_PROP (is_pointer_or_null (p_prev PP)) as PNprev.
  { destruct Sp as [[_ Hk] | (M & E & _ & Hk & Hpl & _)]; rewrite Hprev, Hk;
      [entailer! | sep_apply (hkc5s_pool_pn Tsh (f_t F) TT _ _ Hpl); entailer!]. }
  assert_PROP (is_pointer_or_null (p_cur PP)) as PNcur.
  { destruct Sc as [[_ Hk] | (M & E & _ & Hk & Hpl & _)]; rewrite Hcur, Hk;
      [entailer! | sep_apply (hkc5s_pool_pn Tsh (f_t F) TT _ _ Hpl); entailer!]. }
  assert_PROP (is_pointer_or_null (p_next PP)) as PNnext.
  { destruct Sn as [[_ Hk] | (M & E & _ & Hk & Hpl & _)]; rewrite Hnext, Hk;
      [entailer! | sep_apply (hkc5s_pool_pn Tsh (f_t F) TT _ _ Hpl); entailer!]. }
  assert_PROP (is_pointer_or_null (h5_sp HH)) as PSprev.
  { destruct Sp as [[-> _] | (M & E & HIn & _)]; [entailer! | sep_apply (hkc5s_mk_pn _ _ _ HIn); entailer!]. }
  assert_PROP (is_pointer_or_null (h5_sc HH)) as PScur.
  { destruct Sc as [[-> _] | (M & E & HIn & _)]; [entailer! | sep_apply (hkc5s_mk_pn _ _ _ HIn); entailer!]. }
  assert_PROP (is_pointer_or_null (h5_sn HH)) as PSnext.
  { destruct Sn as [[-> _] | (M & E & HIn & _)]; [entailer! | sep_apply (hkc5s_mk_pn _ _ _ HIn); entailer!]. }
  forward.
  match goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?S0))) _ _ =>
    forward_if (PROPx P0 (LOCALx (temp KC._t'9 (p_prev PP) :: Q0) (SEPx S0))) end.
  { destruct Sp as [[-> _] | (M & E & HIn & _)]; [entailer! | ].
    apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    sep_apply (hkc5s_mkvalid _ _ _ HIn). entailer!. }
  { change (isptr (h5_sp HH)) in H2.
    destruct Sp as [[Hn _] | (M & E & HIn & Hkp & Hpl & _)]; [rewrite Hn in H2; contradiction |].
    assert_PROP (is_pointer_or_null (m5_kp M)) by (sep_apply (hkc5s_pool_pn Tsh (f_t F) TT _ _ Hpl); entailer!).
    destruct (hkc5s_focus _ _ _ HIn) as (nx & Rest & Hf). rewrite Hf. unfold hk5_node. Intros.
    forward. unfold hk5_mk_val. forward. forward.
    rewrite Hprev, Hkp, Hf. unfold hk5_node, hk5_mk_val. entailer!. }
  { destruct Sp as [[_ Hk] | (M & E & _ & _ & _ & Hnn)]; [| contradiction].
    forward. rewrite Hprev, Hk. entailer!. }
  forward.
  match goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?S0))) _ _ =>
    forward_if (PROPx P0 (LOCALx (temp KC._t'10 (Vint Int.zero) :: Q0) (SEPx S0))) end.
  { destruct Sp as [[_ Hk] | (M & E & _ & Hk & Hpl & _)]; rewrite Hprev, Hk; [entailer! |].
    apply denote_tc_test_eq_split; sep_apply (prot3_noise_rot_pool_valid Tsh (f_t F) TT _ _ Hpl); entailer!. }
  { match goal with Hx: ?a <> ?a |- _ => exfalso; apply Hx; reflexivity end. }
  { forward.
    match goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?S0))) _ _ =>
      forward_if (PROPx P0 (LOCALx (temp KC._t'11 (p_cur PP) :: Q0) (SEPx S0))) end.
    { destruct Sc as [[-> _] | (M & E & HIn & _)]; [entailer! | ].
      apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      sep_apply (hkc5s_mkvalid _ _ _ HIn). entailer!. }
    { match goal with Hy: isptr _ |- _ => change (isptr (h5_sc HH)) in Hy end.
      destruct Sc as [[Hn _] | (M & E & HIn & Hkp & Hpl & _)]; [rewrite Hn in *; contradiction |].
      assert_PROP (is_pointer_or_null (m5_kp M)) by (sep_apply (hkc5s_pool_pn Tsh (f_t F) TT _ _ Hpl); entailer!).
      destruct (hkc5s_focus _ _ _ HIn) as (nx & Rest & Hf). rewrite Hf. unfold hk5_node. Intros.
      forward. unfold hk5_mk_val. forward. forward.
      rewrite Hcur, Hkp, Hf. unfold hk5_node, hk5_mk_val. entailer!. }
    { destruct Sc as [[_ Hk] | (M & E & _ & _ & _ & Hnn)]; [| contradiction].
      forward. rewrite Hcur, Hk. entailer!. }
    forward.
    forward.
    { entailer!. destruct Sc as [[_ Hk] | (M & E & _ & Hk & Hpl & _)]; rewrite Hcur, Hk; [entailer! |].
      apply denote_tc_test_eq_split; sep_apply (prot3_noise_rot_pool_valid Tsh (f_t F) TT _ _ Hpl); entailer!. }
    entailer!. rewrite hkc5s_cmp_self by auto. reflexivity. }
  match goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?S0))) _ _ =>
    forward_if (PROPx P0 (LOCALx (temp KC._t'12 (Vint Int.zero) :: Q0) (SEPx S0))) end.
  { match goal with Hx: ?a <> ?a |- _ => exfalso; apply Hx; reflexivity end. }
  { forward.
    match goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?S0))) _ _ =>
      forward_if (PROPx P0 (LOCALx (temp KC._t'13 (p_next PP) :: Q0) (SEPx S0))) end.
    { destruct Sn as [[-> _] | (M & E & HIn & _)]; [entailer! | ].
      apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      sep_apply (hkc5s_mkvalid _ _ _ HIn). entailer!. }
    { match goal with Hy: isptr _ |- _ => change (isptr (h5_sn HH)) in Hy end.
      destruct Sn as [[Hn _] | (M & E & HIn & Hkp & Hpl & _)]; [rewrite Hn in *; contradiction |].
      assert_PROP (is_pointer_or_null (m5_kp M)) by (sep_apply (hkc5s_pool_pn Tsh (f_t F) TT _ _ Hpl); entailer!).
      destruct (hkc5s_focus _ _ _ HIn) as (nx & Rest & Hf). rewrite Hf. unfold hk5_node. Intros.
      forward. unfold hk5_mk_val. forward. forward.
      rewrite Hnext, Hkp, Hf. unfold hk5_node, hk5_mk_val. entailer!. }
    { destruct Sn as [[_ Hk] | (M & E & _ & _ & _ & Hnn)]; [| contradiction].
      forward. rewrite Hnext, Hk. entailer!. }
    forward.
    forward.
    { entailer!. destruct Sn as [[_ Hk] | (M & E & _ & Hk & Hpl & _)]; rewrite Hnext, Hk; [entailer! |].
      apply denote_tc_test_eq_split; sep_apply (prot3_noise_rot_pool_valid Tsh (f_t F) TT _ _ Hpl); entailer!. }
    entailer!. rewrite hkc5s_cmp_self by auto. reflexivity. }
  forward_if.
  { match goal with Hx: ?a <> ?a |- _ => exfalso; apply Hx; reflexivity end. }
  { forward. Exists lk. entailer!. }
Qed.
