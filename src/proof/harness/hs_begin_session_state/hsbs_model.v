(* The law hs_begin_session_state, pure part: the keypair world of A's peer across any number of
   wg_noise_handshake_begin_session calls (begin_session_model, prot_model3.v).

   bsw_inv is the loop invariant of the harness: the facts begin_session's specification requires of the
   peer at p, its keypairs KS and the index table T (hs_in_pool, kps_in_pool, slots_ok), and that no keypair
   lives at the handshake's address.  bsw_inv_step: every call keeps it, whatever the handshake's state, the
   allocation's outcome and the peer's liveness (a successful call adds a keypair and puts the ones its
   slots drop).  bsw_reject: a call in a state other than CREATED_RESPONSE / CONSUMED_RESPONSE returns false
   and changes neither the peer, nor the keypairs, the table or the shim (so not wg_shim_allocs). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require WgNoise.proof.protocol4.prot_specs4.
Local Open Scope Z_scope.

(* the handshake entry of the peer at p is in the pool of T, with share sh *)
Definition bsw_hs (T: tstate) (p: val) (sh: share) : Prop :=
  exists E, sfind (t_D T) (hs_addr p) = Some (sh, E) /\ e_peer E = p.

(* the loop invariant on the peer at p (state P), its keypairs KS and the table T *)
Definition bsw_inv (p: val) (sh: share) (P: peer) (KS: list (val * keypair)) (T: tstate) : Prop :=
  bsw_hs T p sh /\ kps_in_pool T p KS /\ slots_ok P KS /\ ~ In (hs_addr p) (map fst KS).

Lemma bsw_hs_in_pool T p sh : bsw_hs T p sh -> hs_in_pool T p.
Proof. intros [E [H1 H2]]. exists E. unfold t_entry. rewrite H1. auto. Qed.

Lemma bsw_inv_hs p sh P KS T : bsw_inv p sh P KS T -> hs_in_pool T p.
Proof. intros [H _]. eapply bsw_hs_in_pool; eassumption. Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The association lists                                                                            *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma bsw_sfind_sdel {A: Type} (l: list (val * share * A)) a b :
  b <> a -> sfind (sdel l a) b = sfind l b.
Proof.
  intros Hba. induction l as [| [[x sh] v] l IH]; simpl; [reflexivity |].
  destruct (EqDec_val x a) as [-> |]; simpl.
  - destruct (EqDec_val a b); [congruence | reflexivity].
  - destruct (EqDec_val x b); [reflexivity | exact IH].
Qed.

Lemma bsw_sfind_supd {A: Type} (l: list (val * share * A)) a b v :
  sfind (supd l a v) b =
  if eq_dec a b then match sfind l b with Some (sh, _) => Some (sh, v) | None => None end
  else sfind l b.
Proof.
  induction l as [| [[x sh] w] l IH]; simpl.
  - destruct (EqDec_val a b); reflexivity.
  - destruct (EqDec_val x a) as [-> |]; simpl.
    + destruct (EqDec_val a b); reflexivity.
    + rewrite IH. destruct (EqDec_val x b) as [-> |]; [| reflexivity].
      destruct (EqDec_val a b); [congruence | reflexivity].
Qed.

Lemma bsw_adel_fst {A: Type} (l: list (val * A)) a :
  NoDup (map fst l) -> map fst (adel l a) = remove eq_dec a (map fst l).
Proof.
  induction l as [| [x w] l IH]; intros Hnd; simpl; [reflexivity |].
  inv Hnd. destruct (EqDec_val x a) as [-> |]; simpl.
  - destruct (EqDec_val a a) as [_ |]; [| congruence]. rewrite notin_remove by assumption. reflexivity.
  - destruct (EqDec_val a x); [congruence |]. rewrite IH by assumption. reflexivity.
Qed.

Lemma bsw_aupd_fst {A: Type} (l: list (val * A)) a v : map fst (aupd l a v) = map fst l.
Proof.
  induction l as [| [x w] l IH]; simpl; [reflexivity |].
  destruct (EqDec_val x a); simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma bsw_Forall_adel {A: Type} (P: val * A -> Prop) l a : Forall P l -> Forall P (adel l a).
Proof.
  induction l as [| [x w] l IH]; intros H; simpl; [constructor |].
  inv H. destruct (EqDec_val x a); [assumption | constructor; auto].
Qed.

Lemma bsw_Forall_aupd {A: Type} (P: val * A -> Prop) l a v :
  (forall w, P (a, w) -> P (a, v)) -> Forall P l -> Forall P (aupd l a v).
Proof.
  intros Hv. induction l as [| [x w] l IH]; intros H; simpl; [constructor |].
  inv H. destruct (EqDec_val x a) as [-> |]; constructor; eauto.
Qed.

Lemma bsw_In_remove (l: list val) a b : In b (remove eq_dec a l) -> In b l /\ b <> a.
Proof. apply in_remove. Qed.

Lemma bsw_NoDup_remove (l: list val) a : NoDup l -> NoDup (remove eq_dec a l).
Proof.
  induction l as [| x l IH]; intros H; simpl; [constructor |].
  inv H. destruct (EqDec_val a x); [auto |].
  constructor; [| auto]. intros Hin. apply in_remove in Hin. tauto.
Qed.

Lemma bsw_adel_ne {A: Type} (l: list (val * A)) a :
  NoDup (map fst l) -> Forall (fun x => fst x <> a) (adel l a).
Proof.
  induction l as [| [x w] l IH]; intros Hnd; simpl; [constructor |].
  inv Hnd. destruct (EqDec_val x a) as [-> |].
  - rewrite Forall_forall. intros [y v] Hy Hya; simpl in Hya; subst y.
    apply H1. change a with (fst (a, v)). apply in_map. assumption.
  - constructor; [simpl; assumption | auto].
Qed.

Lemma bsw_afind_In {A: Type} (l: list (val * A)) a v : afind l a = Some v -> In a (map fst l).
Proof.
  induction l as [| [x w] l IH]; simpl; [discriminate |].
  destruct (EqDec_val x a); auto.
Qed.

Lemma bsw_sfind_In {A: Type} (l: list (val * share * A)) a sh v : sfind l a = Some (sh, v) -> In a (saddrs l).
Proof.
  induction l as [| [[x sh0] w] l IH]; simpl; [discriminate |].
  destruct (EqDec_val x a); auto.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* One put                                                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

(* the pool facts of the keypairs survive a put; a put keeps every keypair other than its argument *)
Lemma bsw_put_pool p sh k u KS T S :
  kps_in_pool T p KS -> bsw_hs T p sh -> ~ In (hs_addr p) (map fst KS) ->
  let W := kp_put k u (mkKW KS T S) in
  kps_in_pool (kw_T W) p (kw_KS W) /\ bsw_hs (kw_T W) p sh /\ ~ In (hs_addr p) (map fst (kw_KS W)) /\
  (forall a, a <> k -> In a (map fst KS) -> In a (map fst (kw_KS W))).
Proof.
  intros [Hnd Hf] Hhs Hn. unfold kp_put. simpl.
  destruct (EqDec_val k nullval); [simpl; unfold kps_in_pool; auto |].
  destruct (afind KS k) as [K |] eqn:EK; [| simpl; unfold kps_in_pool; auto].
  assert (Ht: forall T0, t_D (if u then t_remove T0 k else T0) = t_D T0)
    by (intros; destruct u; reflexivity).
  assert (Hk: k <> hs_addr p) by (intros ->; apply Hn; eapply bsw_afind_In; eassumption).
  destruct (Int.eq (rc_sub1 (kp_refs K)) Int.zero); simpl.
  - unfold kps_in_pool. rewrite bsw_adel_fst by assumption.
    split; [split |]; [apply bsw_NoDup_remove; assumption | |].
    + pose proof (bsw_adel_ne KS k Hnd) as Hne. pose proof (bsw_Forall_adel _ KS k Hf) as Hf'.
      rewrite Forall_forall in *. intros x Hx. destruct (Hf' x Hx) as [E [H1 H2]].
      exists E. unfold t_free; cbn [t_D]. rewrite bsw_sfind_sdel, Ht by (apply Hne; assumption). auto.
    + split; [| split].
      * destruct Hhs as [E [H1 H2]]. exists E. unfold t_free; cbn [t_D].
        rewrite bsw_sfind_sdel, Ht by congruence. auto.
      * intros Hin. apply in_remove in Hin. tauto.
      * intros a Ha Hin. apply in_in_remove; assumption.
  - unfold kps_in_pool. rewrite bsw_aupd_fst. split; [split |]; [assumption | |].
    + apply bsw_Forall_aupd; [| eapply Forall_impl; [| exact Hf]].
      * intros w [E [H1 H2]]. exists E. simpl in *. auto.
      * intros x [E [H1 H2]]. exists E. rewrite Ht. auto.
    + split; [| split; auto].
      destruct Hhs as [E [H1 H2]]. exists E. rewrite Ht. auto.
Qed.

(* a slot that is not the put keypair stays NULL or live *)
Lemma bsw_put_slot p sh k u KS T S x :
  kps_in_pool T p KS -> bsw_hs T p sh -> ~ In (hs_addr p) (map fst KS) ->
  (x = nullval \/ In x (map fst KS)) -> (x <> nullval -> x <> k) ->
  x = nullval \/ In x (map fst (kw_KS (kp_put k u (mkKW KS T S)))).
Proof.
  intros H1 H2 H3 [Hx | Hx] Hk; [left; assumption |].
  destruct (EqDec_val x nullval) as [-> | Hn]; [left; reflexivity |].
  right. apply (bsw_put_pool p sh k u KS T S H1 H2 H3); auto.
Qed.

(* the slots' distinctness, pairwise *)
Lemma bsw_nodup3 (a b c: val) :
  ((a <> nullval -> a <> b /\ a <> c) /\ (b <> nullval -> b <> c)) ->
  NoDup (filter (fun k => if eq_dec k nullval then false else true) [a; b; c]).
Proof.
  intros [Ha Hb]. simpl.
  destruct (EqDec_val a nullval) as [ea | na]; destruct (EqDec_val b nullval) as [eb | nb];
    destruct (EqDec_val c nullval) as [ec | nc];
    repeat constructor; simpl; try tauto;
    try (specialize (Ha na)); try (specialize (Hb nb)); intuition congruence.
Qed.

Lemma bsw_nodup3_inv (a b c: val) :
  NoDup (filter (fun k => if eq_dec k nullval then false else true) [a; b; c]) ->
  (a <> nullval -> a <> b /\ a <> c) /\ (b <> nullval -> b <> c).
Proof.
  simpl.
  destruct (EqDec_val a nullval) as [ea | na]; destruct (EqDec_val b nullval) as [eb | nb];
    destruct (EqDec_val c nullval) as [ec | nc]; intros H;
    repeat match goal with H: NoDup (_ :: _) |- _ => apply NoDup_cons_iff in H; destruct H end;
    simpl in *; intuition congruence.
Qed.

Lemma bsw_ne_sym (x y: val) : x <> nullval -> (y <> nullval -> y <> x) -> x <> y.
Proof. intros Hx Hy E. subst y. apply Hy; auto. Qed.

(* add_new_keypair(new) with new live and in none of the slots keeps the invariant *)
Lemma bsw_add_new p sh P new init KS T S :
  bsw_inv p sh P KS T -> In new (map fst KS) -> new <> nullval ->
  new <> p_cur P -> new <> p_prev P -> new <> p_next P ->
  let '(P2, W2) := add_new_keypair_model P new init (mkKW KS T S) in
  bsw_inv p sh P2 (kw_KS W2) (kw_T W2) /\ p_device P2 = p_device P /\ p_hs P2 = p_hs P.
Proof.
  intros [Hhs [Hkp [[Hsl Hnd] Hn]]] Hnew Hnn Hc Hp Hx.
  apply bsw_nodup3_inv in Hnd. destruct Hnd as [Hd1 Hd2].
  inv Hsl. inv H2. inv H4. clear H5.
  rename H1 into Sc, H3 into Sp, H2 into Sx.
  unfold add_new_keypair_model.
  destruct init; [match goal with |- context [proj_sumbool ?b] => destruct b as [En | Nn] end; simpl |].
  all: set (cur := p_cur P) in *; set (prev := p_prev P) in *; set (next := p_next P) in *.
  all: destruct (bsw_put_pool p sh prev true KS T S Hkp Hhs Hn) as [K0 [H0 [N0 M0]]].
  - (* initiator, no next: (new, cur, next) after putting prev *)
    split; [| split; reflexivity].
    split; [assumption | split; [assumption | split; [| assumption]]]. split.
    + simpl. repeat apply Forall_cons; try apply Forall_nil.
      * right. apply M0; [congruence | assumption].
      * apply (bsw_put_slot p sh); auto. intros Hcn. apply Hd1; assumption.
      * left; assumption.
    + apply bsw_nodup3. simpl. split; [intros _; split; congruence | intros Hcn; congruence].
  - (* initiator with a next: (new, next, NULL) after putting cur and prev *)
    destruct (bsw_put_pool p sh cur true KS T S Hkp Hhs Hn) as [K1 [H1 [N1 M1]]].
    destruct (kp_put cur true (mkKW KS T S)) as [KS1 T1 S1] eqn:EW1. simpl in K1, H1, N1, M1.
    destruct (bsw_put_pool p sh prev true KS1 T1 S1 K1 H1 N1) as [K2 [H2 [N2 M2]]].
    assert (Nc: next <> cur) by (apply bsw_ne_sym; [assumption | intros h; apply Hd1; assumption]).
    assert (Np: next <> prev) by (apply bsw_ne_sym; [assumption | assumption]).
    split; [| split; reflexivity].
    split; [assumption | split; [assumption | split; [| assumption]]]. split.
    + simpl. repeat apply Forall_cons; try apply Forall_nil.
      * right. apply M2; [congruence |]. apply M1; [congruence | assumption].
      * right. destruct Sx as [Sx | Sx]; [congruence |]. apply M2; [assumption |]. apply M1; assumption.
      * left; reflexivity.
    + apply bsw_nodup3. simpl. split; [intros _; split; congruence | intros _; congruence].
  - (* responder: (cur, NULL, new) after putting next and prev *)
    simpl.
    destruct (bsw_put_pool p sh next true KS T S Hkp Hhs Hn) as [K1 [H1 [N1 M1]]].
    destruct (kp_put next true (mkKW KS T S)) as [KS1 T1 S1] eqn:EW1. simpl in K1, H1, N1, M1.
    destruct (bsw_put_pool p sh prev true KS1 T1 S1 K1 H1 N1) as [K2 [H2 [N2 M2]]].
    split; [| split; reflexivity].
    split; [assumption | split; [assumption | split; [| assumption]]]. split.
    + simpl. repeat apply Forall_cons; try apply Forall_nil.
      * destruct Sc as [Sc | Sc]; [left; assumption |].
        destruct (EqDec_val cur nullval) as [E0 | E0]; [left; assumption | right].
        destruct (Hd1 E0) as [Hcp Hcn].
        apply M2; [assumption |]. apply M1; assumption.
      * left; reflexivity.
      * right. apply M2; [congruence |]. apply M1; [congruence | assumption].
    + apply bsw_nodup3. simpl. split; [intros h; split; congruence | intros h; congruence].
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The table steps of a successful call                                                              *)
(* ------------------------------------------------------------------------------------------------ *)

(* replace keeps every pool entry, with its share and its peer (it only sets the new entry's index) *)
Lemma bsw_replace_sfind T old new a sh E :
  sfind (t_D T) a = Some (sh, E) ->
  exists E', sfind (t_D (snd (t_replace T old new))) a = Some (sh, E') /\ e_peer E' = e_peer E.
Proof.
  intros H. unfold t_replace. destruct (vin old (t_L T)); simpl; [| eauto].
  unfold t_set_index, t_entry. destruct (sfind (t_D T) new) as [[sh0 E0] |] eqn:En; simpl; [| eauto].
  rewrite bsw_sfind_supd. destruct (EqDec_val new a) as [-> | Hne].
  - rewrite H in En. inv En. rewrite H.
    match goal with |- context [if ?b then _ else _] => destruct b; [| congruence] end.
    eexists; split; [reflexivity |]. reflexivity.
  - match goal with |- context [if ?b then _ else _] => destruct b; [congruence |] end. eauto.
Qed.

Lemma bsw_replace_inv p sh P KS T old new :
  bsw_inv p sh P KS T -> bsw_inv p sh P KS (snd (t_replace T old new)).
Proof.
  intros [[E [H1 H2]] [[Hnd Hf] [Hs Hn]]]. split; [| split; [split |]; auto].
  - destruct (bsw_replace_sfind T old new _ _ _ H1) as [E' [H3 H4]].
    exists E'. split; [assumption | congruence].
  - eapply Forall_impl; [| exact Hf]. intros x [E0 [H3 H4]].
    destruct (bsw_replace_sfind T old new _ _ _ H3) as [E' [H5 H6]]. exists E'.
    split; [assumption | rewrite H6; assumption].
Qed.

(* the new keypair's unhashed entry joins the pool *)
Lemma bsw_add_inv p sh P KS T k K E :
  bsw_inv p sh P KS T -> e_peer E = p -> ~ In k (saddrs (t_D T)) -> ~ In k (map fst KS) ->
  bsw_inv p sh P ((k, K) :: KS) (t_add T k Ews E).
Proof.
  intros [[E0 [H1 H2]] [[Hnd Hf] [[Hs Hd] Hn]]] He HkT HkK.
  assert (Hkh: k <> hs_addr p).
  { intros ->. apply HkT. eapply bsw_sfind_In; eassumption. }
  split; [| split; [split |]].
  - exists E0. unfold t_add. simpl. destruct (EqDec_val k (hs_addr p)); [congruence |]. auto.
  - simpl. constructor; assumption.
  - constructor.
    + exists E. simpl. destruct (EqDec_val k k); [auto | congruence].
    + rewrite Forall_forall in *. intros [x v] Hx. destruct (Hf _ Hx) as [E1 [H3 H4]]. exists E1.
      simpl in *. destruct (EqDec_val k x) as [-> |]; [| auto].
      exfalso. apply HkK. change x with (fst (x, v)). apply in_map. assumption.
  - split; [split; [| assumption] |].
    + eapply Forall_impl; [| exact Hs]. simpl. tauto.
    + simpl. intros [? | ?]; auto.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* begin_session                                                                                    *)
(* ------------------------------------------------------------------------------------------------ *)

(* every call keeps the invariant, the peer's device, and its slots unless it succeeds; k is the address
   kzalloc returned, fresh by begin_session's specification *)
Lemma bsw_inv_step P p sh k kc KS T S :
  bsw_inv p sh P KS T -> (k <> nullval -> ~ In k (saddrs (t_D T)) /\ ~ In k (map fst KS)) ->
  let '(b, P', W', kc') := begin_session_model P (hs_addr p) k kc (mkKW KS T S) in
  bsw_inv p sh P' (kw_KS W') (kw_T W') /\ p_device P' = p_device P.
Proof.
  intros Hi Hk. unfold begin_session_model. cbn [kw_KS kw_T kw_S].
  destruct (negb _); [split; auto |].
  destruct (eq_dec k nullval) as [Kn | Kn]; [split; auto |].
  destruct (Hk Kn) as [HkT HkK].
  destruct (p_dead P); [split; auto |].
  assert (He: e_peer_of_hs (mkKW KS T S) (hs_addr p) = p).
  { destruct Hi as [[E [H1 H2]] _]. unfold e_peer_of_hs, t_entry. simpl. rewrite H1. assumption. }
  rewrite He.
  set (K := kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S)).
  set (E := mkEntry p IDX_KEYPAIR Int.zero).
  pose proof (bsw_add_inv p sh P KS T k K E Hi eq_refl HkT HkK) as Hi1.
  set (P1 := p_set_hs P (hs_zero (p_hs P))).
  assert (Hi1': bsw_inv p sh P1 ((k, K) :: KS) (t_add T k Ews E)) by exact Hi1.
  destruct Hi as [_ [_ [[Hs Hd] _]]].
  assert (Hslot: forall x, In x [p_cur P; p_prev P; p_next P] -> k <> x).
  { intros x Hx Ex. subst x. rewrite Forall_forall in Hs. destruct (Hs k Hx); auto. }
  pose proof (bsw_add_new p sh P1 k (kp_init K) ((k, K) :: KS) (t_add T k Ews E)
                (shim_alloc_ok S) Hi1' (or_introl eq_refl) Kn) as Ha.
  destruct (add_new_keypair_model P1 k (kp_init K) _) as [P2 W2] eqn:EA.
  destruct Ha as [Hi2 [Hd2 _]]; [apply Hslot; simpl; auto .. |].
  destruct (t_replace (kw_T W2) (hs_addr p) k) as [ok T3] eqn:ER. cbn [kw_KS kw_T].
  split; [| rewrite Hd2; reflexivity].
  replace T3 with (snd (t_replace (kw_T W2) (hs_addr p) k)) by (rewrite ER; reflexivity).
  apply bsw_replace_inv. assumption.
Qed.

(* a call in a state other than CREATED_RESPONSE / CONSUMED_RESPONSE returns false and changes nothing *)
Lemma bsw_reject P p k kc KS T S :
  Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE = false ->
  Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE = false ->
  begin_session_model P (hs_addr p) k kc (mkKW KS T S) = (false, P, mkKW KS T S, kc).
Proof. intros H1 H2. unfold begin_session_model. rewrite H1, H2. reflexivity. Qed.

(* the invariant holds for new_pair's peer (no keypairs, its handshake entry alone in the pool) and does
   not depend on the handshake the harness writes before each call *)
Lemma bsw_inv_init pa sh P :
  p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  bsw_inv pa sh P [] (mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE Int.zero)] []).
Proof.
  intros Hc Hp Hn. split; [| split; [| split]].
  - exists (mkEntry pa IDX_HANDSHAKE Int.zero). simpl.
    destruct (EqDec_val (hs_addr pa) (hs_addr pa)); [auto | congruence].
  - split; constructor.
  - unfold slots_ok. rewrite Hc, Hp, Hn. split.
    + repeat constructor.
    + simpl. destruct (eq_dec nullval nullval); [constructor | congruence].
  - simpl. tauto.
Qed.

Lemma bsw_inv_set_hs p sh P H KS T : bsw_inv p sh P KS T -> bsw_inv p sh (p_set_hs P H) KS T.
Proof. intros Hi. exact Hi. Qed.
