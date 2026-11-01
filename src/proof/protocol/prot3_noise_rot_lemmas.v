(* The peer without its slots, the keypair list split at one keypair, a pool entry's valid pointer,
   and the invariants kept by kp_put. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* ------------------------------------------------------------------------------------------------ *)
(* Pure facts                                                                                       *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma prot3_noise_rot_kw_eta (W: kworld) : mkKW (kw_KS W) (kw_T W) (kw_S W) = W.
Proof. destruct W; reflexivity. Qed.

Lemma prot3_noise_rot_afind_in {A: Type} (KS: list (val * A)) k :
  In k (map fst KS) -> exists K, afind KS k = Some K.
Proof.
  induction KS as [|[x v] KS IH]; simpl; [tauto|].
  intros Hin. destruct (EqDec_val x k); [eauto|].
  destruct Hin as [E|H]; [simpl in E; congruence | auto].
Qed.

Lemma prot3_noise_rot_afind_some_in {A: Type} (KS: list (val * A)) k K :
  afind KS k = Some K -> In k (map fst KS).
Proof.
  induction KS as [|[x v] KS IH]; simpl; [discriminate|].
  destruct (EqDec_val x k); auto.
Qed.

Lemma prot3_noise_rot_map_fst_aupd {A: Type} (KS: list (val * A)) k K :
  map fst (aupd KS k K) = map fst KS.
Proof.
  induction KS as [|[x v] KS IH]; simpl; auto.
  destruct (EqDec_val x k); simpl; f_equal; auto.
Qed.

Lemma prot3_noise_rot_in_adel {A: Type} (KS: list (val * A)) k x :
  In x (adel KS k) -> In x KS.
Proof.
  induction KS as [|[y v] KS IH]; simpl; auto.
  destruct (EqDec_val y k); simpl; auto. intros [E|H]; auto.
Qed.

Lemma prot3_noise_rot_in_adel_neq {A: Type} (KS: list (val * A)) k x :
  NoDup (map fst KS) -> In x (adel KS k) -> fst x <> k.
Proof.
  induction KS as [|[y v] KS IH]; simpl; [tauto|].
  intros ND. inversion ND; subst.
  destruct (EqDec_val y k).
  - subst. intros Hin E. apply H1. rewrite <- E. apply in_map. auto.
  - simpl. intros [E|Hin]; [subst; simpl; auto|]. apply IH; auto.
Qed.

Lemma prot3_noise_rot_map_fst_adel_in {A: Type} (KS: list (val * A)) k x :
  x <> k -> In x (map fst KS) -> In x (map fst (adel KS k)).
Proof.
  induction KS as [|[y v] KS IH]; simpl; auto.
  intros N [E|H]; destruct (EqDec_val y k); subst; simpl; auto; congruence.
Qed.

Lemma prot3_noise_rot_nodup_adel {A: Type} (KS: list (val * A)) k :
  NoDup (map fst KS) -> NoDup (map fst (adel KS k)).
Proof.
  induction KS as [|[y v] KS IH]; simpl; auto.
  intros ND. inversion ND; subst.
  destruct (EqDec_val y k); auto. simpl. constructor; auto.
  intros Hin. apply H1. apply in_map_iff in Hin. destruct Hin as [[a b] [E Hin]]. simpl in E. subst.
  apply prot3_noise_rot_in_adel in Hin. apply (in_map fst) in Hin. auto.
Qed.

Lemma prot3_noise_rot_sfind_sdel {A: Type} (D: list (val * share * A)) a b :
  b <> a -> sfind (sdel D a) b = sfind D b.
Proof.
  intros N. induction D as [|[[x sh] v] D IH]; simpl; auto.
  destruct (EqDec_val x a); simpl.
  - subst. destruct (EqDec_val a b); [congruence | auto].
  - destruct (EqDec_val x b); auto.
Qed.

(* kp_put keeps the pool invariant and the other keypairs *)
Lemma prot3_noise_rot_put_in_pool T p KS S k u :
  kps_in_pool T p KS ->
  kps_in_pool (kw_T (kp_put k u (mkKW KS T S))) p (kw_KS (kp_put k u (mkKW KS T S))).
Proof.
  intros [ND F]. unfold kp_put. simpl.
  destruct (EqDec_val k nullval); [split; auto|].
  destruct (afind KS k) as [K|] eqn:Hf; [|split; auto].
  set (T1 := if u then t_remove T k else T).
  assert (HD: t_D T1 = t_D T) by (subst T1; destruct u; reflexivity).
  destruct (Int.eq (rc_sub1 (kp_refs K)) Int.zero); simpl.
  - split; [apply prot3_noise_rot_nodup_adel; auto|].
    rewrite Forall_forall in F |- *. intros x Hin.
    pose proof (prot3_noise_rot_in_adel_neq _ _ _ ND Hin) as Nx.
    apply prot3_noise_rot_in_adel in Hin. destruct (F x Hin) as [E [HE HP]].
    exists E. split; auto. unfold t_free. simpl. rewrite prot3_noise_rot_sfind_sdel by auto.
    rewrite HD. auto.
  - split; [rewrite prot3_noise_rot_map_fst_aupd; auto|].
    rewrite HD. clear Hf. induction KS as [|[y v] KS IH]; simpl; auto.
    simpl in ND. inversion ND; subst. inversion F; subst.
    destruct (EqDec_val y k); constructor; auto.
Qed.

Lemma prot3_noise_rot_put_keeps T KS S k u k2 :
  k2 <> k -> In k2 (map fst KS) -> In k2 (map fst (kw_KS (kp_put k u (mkKW KS T S)))).
Proof.
  intros N Hin. unfold kp_put. simpl.
  destruct (EqDec_val k nullval); auto.
  destruct (afind KS k) as [K|]; auto.
  destruct (Int.eq (rc_sub1 (kp_refs K)) Int.zero); simpl.
  - apply prot3_noise_rot_map_fst_adel_in; auto.
  - rewrite prot3_noise_rot_map_fst_aupd; auto.
Qed.

Lemma prot3_noise_rot_put_D T KS S k u :
  t_D (kw_T (kp_put k u (mkKW KS T S))) = t_D T \/
  t_D (kw_T (kp_put k u (mkKW KS T S))) = sdel (t_D T) k.
Proof.
  unfold kp_put. simpl.
  destruct (EqDec_val k nullval); auto.
  destruct (afind KS k) as [K|]; auto.
  destruct (Int.eq (rc_sub1 (kp_refs K)) Int.zero); simpl; destruct u; auto.
Qed.

(* the slots of a peer *)
Lemma prot3_noise_rot_slots P KS :
  slots_ok P KS ->
  (p_cur P = nullval \/ In (p_cur P) (map fst KS)) /\
  (p_prev P = nullval \/ In (p_prev P) (map fst KS)) /\
  (p_next P = nullval \/ In (p_next P) (map fst KS)) /\
  (p_cur P <> nullval -> p_cur P <> p_prev P /\ p_cur P <> p_next P) /\
  (p_prev P <> nullval -> p_prev P <> p_next P).
Proof.
  intros [F ND]. inversion F as [|? ? Hc F1]; subst. inversion F1 as [|? ? Hp F2]; subst.
  inversion F2 as [|? ? Hn _]; subst.
  split; [auto|]. split; [auto|]. split; [auto|].
  revert ND. generalize (p_cur P) (p_prev P) (p_next P). intros c pr n ND. simpl in ND.
  split.
  - intros Nc. destruct (EqDec_val c nullval); [contradiction|].
    inversion ND as [|? ? Nin ND1]; subst.
    split; intros E; subst; apply Nin.
    + destruct (EqDec_val pr nullval); [contradiction|]. left; auto.
    + destruct (EqDec_val pr nullval); [|right]; destruct (EqDec_val n nullval); try contradiction; simpl; auto.
  - intros Np. destruct (EqDec_val c nullval); [|inversion ND as [|? ? _ ND']; clear ND; rename ND' into ND];
      destruct (EqDec_val pr nullval); try contradiction;
      inversion ND as [|? ? Nin _]; subst; intros E; subst; apply Nin;
      destruct (EqDec_val n nullval); try contradiction; simpl; auto.
Qed.

Lemma prot3_noise_rot_in_pool T p KS k :
  kps_in_pool T p KS -> In k (map fst KS) -> exists E, sfind (t_D T) k = Some (Ews, E) /\ e_peer E = p.
Proof.
  intros [_ F] Hin. apply in_map_iff in Hin. destruct Hin as [x [E Hx]]. subst.
  rewrite Forall_forall in F. auto.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* Separation facts                                                                                 *)
(* ------------------------------------------------------------------------------------------------ *)

(* the peer without its keypair slots *)
Definition prot3_noise_rot_peer_rest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma prot3_noise_rot_peer_split sh p P :
  peer_rep sh p P =
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) * prot3_noise_rot_peer_rest sh p P.
Proof.
  unfold peer_rep, prot3_noise_rot_peer_rest. apply pred_ext; entailer!; cancel.
Qed.

Lemma prot3_noise_rot_peer_rest_slots sh p P a b c :
  prot3_noise_rot_peer_rest sh p (p_set_slots P a b c) = prot3_noise_rot_peer_rest sh p P.
Proof. reflexivity. Qed.

(* the peer's keypairs struct as a field of the peer *)
Lemma prot3_noise_rot_kps_field sh p v :
  field_compatible t_peer [] p ->
  data_at sh t_kps v (kps_addr p) = field_at sh t_peer [StructField I._keypairs] v p.
Proof.
  intros FC. rewrite field_at_data_at. f_equal.
  rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Section KS.
Variable CSw: compspecs.

Lemma prot3_noise_rot_ks_split KS k K :
  afind KS k = Some K ->
  keypairs_rep CSw KS = keypair_rep CSw k K * keypairs_rep CSw (adel KS k).
Proof.
  unfold keypairs_rep. induction KS as [|[x v] KS IH]; simpl; [discriminate|].
  destruct (EqDec_val x k).
  - intros E; inversion E; subst. reflexivity.
  - intros Hf. simpl. rewrite (IH Hf). rewrite <- !sepcon_assoc. f_equal. apply sepcon_comm.
Qed.

Lemma prot3_noise_rot_ks_upd KS k K K' :
  afind KS k = Some K ->
  keypairs_rep CSw (aupd KS k K') = keypair_rep CSw k K' * keypairs_rep CSw (adel KS k).
Proof.
  unfold keypairs_rep. induction KS as [|[x v] KS IH]; simpl; [discriminate|].
  destruct (EqDec_val x k).
  - intros E; inversion E; subst. reflexivity.
  - intros Hf. simpl. rewrite (IH Hf). rewrite <- !sepcon_assoc. f_equal. apply sepcon_comm.
Qed.

End KS.

(* a pool entry's address is a valid pointer *)
Lemma prot3_noise_rot_iter_sfind {A: Type} (f: val * share * A -> mpred) D a sh v :
  sfind D a = Some (sh, v) -> iter_sepcon f D = f (a, sh, v) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x s] w] D IH]; simpl; [discriminate|].
  destruct (EqDec_val x a).
  - intros E; inversion E; subst. reflexivity.
  - intros Hf. simpl. rewrite (IH Hf). rewrite <- !sepcon_assoc. f_equal. apply sepcon_comm.
Qed.

Lemma prot3_noise_rot_pool_valid sht tab T a E :
  sfind (t_D T) a = Some (Ews, E) -> itable sht tab T |-- valid_pointer a.
Proof.
  intros Hf. unfold itable. rewrite (prot3_noise_rot_iter_sfind _ _ _ _ _ Hf).
  apply andp_left2. apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  simpl. unfold entry_at. apply data_at_valid_ptr; [auto | reflexivity].
Qed.

Lemma prot3_noise_rot_kp_valid sht tab T p KS k :
  kps_in_pool T p KS -> In k (map fst KS) -> itable sht tab T |-- valid_pointer k.
Proof.
  intros HP Hin. destruct (prot3_noise_rot_in_pool _ _ _ _ HP Hin) as [E [Hf _]].
  eapply prot3_noise_rot_pool_valid; eauto.
Qed.

Lemma prot3_noise_rot_ks_ptrs CSw KS :
  keypairs_rep CSw KS |-- !! (forall k, In k (map fst KS) -> isptr k).
Proof.
  unfold keypairs_rep. induction KS as [|[x K] KS IH]; simpl.
  - apply prop_right. tauto.
  - unfold keypair_rep at 1. Intros. sep_apply IH. Intros. apply prop_right.
    intros k [E|Hin]; [subst; exact (@field_compatible_isptr Noise.CS _ _ _ H) | auto].
Qed.

Lemma prot3_noise_rot_slot_ptr (KS: list (val * keypair)) k :
  (forall k, In k (map fst KS) -> isptr k) -> k = nullval \/ In k (map fst KS) -> is_pointer_or_null k.
Proof.
  intros HP [E|Hin]; [subst; reflexivity|]. apply HP in Hin. destruct k; try contradiction; exact I.
Qed.

(* the peer without its slots and its last_sent_handshake *)
Definition prot3_noise_rot_peer_rest2 (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   hs_rep sh (hs_addr p) (p_hs P) *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma prot3_noise_rot_peer_rest_lsh sh p P :
  prot3_noise_rot_peer_rest sh p P =
  data_at sh t_atomic64 (Vlong (p_lsh P)) (field_address t_peer [StructField I._last_sent_handshake] p) *
  prot3_noise_rot_peer_rest2 sh p P.
Proof.
  unfold prot3_noise_rot_peer_rest, prot3_noise_rot_peer_rest2.
  apply pred_ext; Intros; rewrite field_at_data_at; entailer!; cancel.
Qed.

Lemma prot3_noise_rot_peer_rest2_lsh sh p P l :
  prot3_noise_rot_peer_rest2 sh p (p_set_lsh P l) = prot3_noise_rot_peer_rest2 sh p P.
Proof. reflexivity. Qed.

(* expire's invalidation of one slot (as in expire_model) *)
Definition prot3_noise_rot_inv (KS: list (val * keypair)) (k: val) : list (val * keypair) :=
  if eq_dec k nullval then KS else
  match afind KS k with Some K => aupd KS k (kp_invalidate_send K) | None => KS end.

Lemma prot3_noise_rot_inv_map_fst KS k : map fst (prot3_noise_rot_inv KS k) = map fst KS.
Proof.
  unfold prot3_noise_rot_inv. destruct (eq_dec k nullval); auto.
  destruct (afind KS k); auto. apply prot3_noise_rot_map_fst_aupd.
Qed.

Lemma prot3_noise_rot_expire_KS P hs KS T now :
  snd (fst (expire_model P hs KS T now)) =
  prot3_noise_rot_inv (prot3_noise_rot_inv KS (p_next P)) (p_cur P).
Proof. reflexivity. Qed.

Lemma prot3_noise_rot_kps_in_pool_remove T a p KS :
  kps_in_pool T p KS -> kps_in_pool (t_remove T a) p KS.
Proof. auto. Qed.

Lemma prot3_noise_rot_expire_P P hs KS T now :
  fst (fst (expire_model P hs KS T now)) = p_set_lsh (p_set_hs P (hs_zero (p_hs P))) (reset_lsh now).
Proof. reflexivity. Qed.

Lemma prot3_noise_rot_expire_T P hs KS T now :
  snd (expire_model P hs KS T now) = t_remove T hs.
Proof. reflexivity. Qed.

(* the NULL test of a pointer that is NULL or valid *)
Local Transparent denote_tc_test_eq.
Lemma prot3_noise_rot_tc_null (R: mpred) k :
  k = nullval \/ (isptr k /\ (R |-- valid_pointer k)) -> R |-- denote_tc_test_eq k (Vlong Int64.zero).
Proof.
  intros [E|[Pk VP]].
  - subst. unfold nullval, denote_tc_test_eq. simpl. apply andp_right; apply prop_right; auto.
  - destruct k; try contradiction. unfold denote_tc_test_eq. simpl. apply andp_right; [apply prop_right; auto|].
    apply valid_pointer_weak'. exact VP.
Qed.

(* a valid pointer from one conjunct of a product *)
Ltac prot3_vp VP :=
  repeat first [ exact VP | simple apply (sepcon_valid_pointer2 _ _ _ VP) | apply sepcon_valid_pointer1 ].

(* the model of add_new_keypair / received_with_keypair, case by case *)
Lemma prot3_noise_rot_add_init_null P new W :
  p_next P = nullval ->
  add_new_keypair_model P new true W = (p_set_slots P new (p_cur P) nullval, kp_put (p_prev P) true W).
Proof.
  intros E. unfold add_new_keypair_model. rewrite E. destruct (eq_dec nullval nullval); [|congruence].
  reflexivity.
Qed.

Lemma prot3_noise_rot_add_init_next P new W :
  p_next P <> nullval ->
  add_new_keypair_model P new true W =
  (p_set_slots P new (p_next P) nullval, kp_put (p_prev P) true (kp_put (p_cur P) true W)).
Proof.
  intros E. unfold add_new_keypair_model. destruct (eq_dec (p_next P) nullval); [contradiction|].
  reflexivity.
Qed.

Lemma prot3_noise_rot_add_resp P new W :
  add_new_keypair_model P new false W =
  (p_set_slots P (p_cur P) nullval new, kp_put (p_prev P) true (kp_put (p_next P) true W)).
Proof. reflexivity. Qed.

Lemma prot3_noise_rot_recv_eq P k W :
  k = p_next P ->
  received_with_keypair_model P k W = (true, p_set_slots P k (p_cur P) nullval, kp_put (p_prev P) true W).
Proof.
  intros E. unfold received_with_keypair_model. destruct (eq_dec k (p_next P)); [reflexivity | contradiction].
Qed.

Lemma prot3_noise_rot_recv_neq P k W :
  k <> p_next P -> received_with_keypair_model P k W = (false, P, W).
Proof.
  intros E. unfold received_with_keypair_model. destruct (eq_dec k (p_next P)); [contradiction | reflexivity].
Qed.

Section KP.
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

(* a keypair without its i_am_the_initiator field *)
Definition prot3_noise_rot_kp_rest (k: val) (K: keypair) : mpred :=
  !! (field_compatible t_kp [] k /\ kp_ok K) &&
  (@malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k *
   field_at Ews t_kp [StructField I._sending] (symkey_val (kp_send K)) k *
   field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
   field_at Ews t_kp [StructField I._receiving] (symkey_val (kp_recv K)) k *
   (EX lk: val, field_at Ews t_kp [StructField I._receiving_counter]
                   (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k) *
   field_at Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k *
   field_at Ews t_kp [StructField I._refcount] (Vint (kp_refs K)) k *
   (EX r: val, field_at Ews t_kp [StructField I._rcu] r k) *
   field_at Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
   spacer Ews 1181 1184 k).

Lemma prot3_noise_rot_kp_init_split k K :
  keypair_rep CSw k K =
  field_at Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k *
  prot3_noise_rot_kp_rest k K.
Proof.
  unfold keypair_rep, prot3_noise_rot_kp_rest.
  apply pred_ext; Intros a b; Exists a b; entailer!.
Qed.

End KP.

(* pointer comparisons of a keypair with a slot *)
Local Transparent denote_tc_test_eq.
Lemma prot3_noise_rot_tc_ptrs (R: mpred) k n :
  isptr k -> (R |-- valid_pointer k) -> n = nullval \/ (isptr n /\ (R |-- valid_pointer n)) ->
  R |-- denote_tc_test_eq k n.
Proof.
  intros Pk VK [E|[Pn VN]].
  - subst. destruct k; try contradiction. unfold nullval, denote_tc_test_eq. simpl.
    apply andp_right; [apply prop_right; auto|]. apply valid_pointer_weak'. exact VK.
  - destruct k; try contradiction. destruct n; try contradiction. unfold denote_tc_test_eq. simpl.
    unfold test_eq_ptrs. destruct (sameblock _ _); apply andp_right; auto; apply valid_pointer_weak'; auto.
Qed.

Lemma prot3_noise_rot_cmp_eq t k n :
  isptr k -> n = nullval \/ isptr n ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr t) (tptr t) k n)) =
  Val.of_bool (if eq_dec k n then true else false).
Proof.
  intros Pk Hn. destruct k; try contradiction.
  destruct Hn as [E|Pn].
  - subst. destruct (eq_dec (Vptr b i) nullval) as [E|_]; [discriminate|].
    unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r. reflexivity.
  - destruct n; try contradiction. destruct (eq_dec (Vptr b i) (Vptr b0 i0)) as [E|NE].
    + inversion E; subst. unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r.
      unfold sem_cmp_pp. simpl. destruct (eq_block b0 b0); [|congruence]. simpl. rewrite Ptrofs.eq_true. reflexivity.
    + unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r.
      unfold sem_cmp_pp. simpl. destruct (eq_block b b0).
      * subst. simpl. destruct (Ptrofs.eq i i0) eqn:Ei; [|reflexivity].
        apply Ptrofs.same_if_eq in Ei. subst. congruence.
      * reflexivity.
Qed.

Lemma prot3_noise_rot_cmp_ne t k :
  isptr k -> eval_binop Cop.One (tptr t) (tptr t) k k = Vint Int.zero.
Proof.
  intros Pk. destruct k; try contradiction.
  unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r.
  unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl. rewrite Ptrofs.eq_true. reflexivity.
Qed.
