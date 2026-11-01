(* The law hs_begin_session_state: what main needs to read and compare A's keypair slots, and to give back
   struct pair at its return.  A slot is NULL or a live keypair (slots_ok); a live keypair is a pointer
   (keypair_rep), and a valid one: its entry, at its own address, is in the index table's pool
   (kps_in_pool). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_close.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_model.
Local Open Scope logic.

Lemma hbs_kps_isptr CSw KS : keypairs_rep CSw KS |-- !! Forall (fun x => isptr (fst x)) KS.
Proof.
  unfold keypairs_rep. induction KS as [| [k K] KS IH]; simpl.
  - entailer!.
  - unfold keypair_rep at 1. sep_apply IH. entailer!.
    constructor; [simpl; destruct H0 as [Hp _]; exact Hp | assumption].
Qed.

Lemma hbs_slots_ptr CSw P KS :
  slots_ok P KS ->
  keypairs_rep CSw KS |--
  !! (is_pointer_or_null (p_cur P) /\ is_pointer_or_null (p_prev P) /\ is_pointer_or_null (p_next P)).
Proof.
  intros [Hs _]. eapply derives_trans; [apply (hbs_kps_isptr CSw KS) |]. apply prop_derives. intros Hp.
  assert (G: forall k, k = nullval \/ In k (map fst KS) -> is_pointer_or_null k).
  { intros k [-> | Hk]; [simpl; auto |].
    apply in_map_iff in Hk. destruct Hk as [[k' K] [<- Hin]].
    rewrite Forall_forall in Hp. specialize (Hp _ Hin). simpl in Hp. destruct k'; try contradiction; simpl; auto. }
  inv Hs. inv H2. inv H4. auto.
Qed.

Lemma hbs_sfind_In_elem {A: Type} (l: list (val * share * A)) a sh v :
  sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [| [[x sh0] w] l IH]; simpl; [discriminate |].
  destruct (EqDec_val x a) as [-> |]; [intros H; inv H; left; reflexivity | right; auto].
Qed.

(* a live keypair of the peer is a valid pointer: its entry is in the pool *)
Lemma hbs_kp_valid sht tab T p KS k :
  kps_in_pool T p KS -> In k (map fst KS) -> itable sht tab T |-- valid_pointer k.
Proof.
  intros [_ Hf] Hk. apply in_map_iff in Hk. destruct Hk as [[k' K] [<- Hin]].
  rewrite Forall_forall in Hf. destruct (Hf _ Hin) as [E [H1 _]]. simpl in H1.
  apply hbs_sfind_In_elem in H1.
  unfold itable. Intros.
  apply sepcon_valid_pointer2.
  sep_apply (iter_sepcon_in_true (pool_item_rep (t_L T)) (t_D T) _ H1).
  apply sepcon_valid_pointer1. unfold pool_item_rep, entry_at.
  auto with valid_pointer.
Qed.

(* comparing a slot with itself (x == x in C) is defined: x is NULL or a live keypair *)
Lemma hbs_test_eq_self sht tab T p KS x Q :
  kps_in_pool T p KS -> x = nullval \/ In x (map fst KS) ->
  itable sht tab T * Q |-- denote_tc_test_eq x x.
Proof.
  intros Hk Hx.
  assert (V: itable sht tab T * Q |-- valid_pointer x).
  { destruct Hx as [-> | Hx]; [apply valid_pointer_null |].
    apply sepcon_valid_pointer1; eapply hbs_kp_valid; eassumption. }
  apply denote_tc_test_eq_split; exact V.
Qed.

(* x == x is 1 for a pointer or NULL *)
Lemma hbs_eq_self {cs: compspecs} t x : is_pointer_or_null x -> eval_binop Oeq (tptr t) (tptr t) x x = Vint Int.one.
Proof.
  intros H. unfold eval_binop, force_val2, sem_binary_operation', sem_cmp, sem_cmp_pp. simpl.
  rewrite !andb_false_r. simpl.
  destruct x; try contradiction.
  - simpl in H. subst i. reflexivity.
  - unfold Val.cmplu_bool. simpl. destruct (eq_block b b); [| congruence].
    rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hbs_cmp_self x : is_pointer_or_null x -> sem_cmp_pp Ceq x x = Some (Vint Int.one).
Proof.
  intros H. unfold sem_cmp_pp. destruct x; try contradiction.
  - simpl in H. subst i. reflexivity.
  - unfold Val.cmplu_bool. simpl. destruct (eq_block b b); [| congruence].
    rewrite Ptrofs.eq_true. reflexivity.
Qed.

(* the pool item of an entry found in the pool *)
Lemma hbs_pool_take T a sh E :
  sfind (t_D T) a = Some (sh, E) ->
  iter_sepcon hs_pool_entry (t_D T) |-- EX n: val, EX h: bool, entry_at sh a E n h * TT.
Proof.
  intros H. apply hbs_sfind_In_elem in H.
  sep_apply (iter_sepcon_in_true hs_pool_entry (t_D T) _ H). unfold hs_pool_entry.
  Intros n h. Exists n h. cancel.
Qed.

(* struct pair at the end of main: the devices, the tables (each holding its peer's handshake entry, A's also
   the keypairs' entries), the public-key tables and the peers give back the struct's memory; the keypairs'
   entries are dropped (TT) *)
Lemma hbs_close sh p DA DB TA TB ka kb PA PB :
  @field_compatible CSh t_pair [] p -> bsw_hs TA (pair_ap p) sh -> bsw_hs TB (pair_bp p) sh ->
  device_rep5 sh (pair_a p) DA * device_rep5 sh (pair_b p) DB *
  itable sh (pair_ai p) TA * itable sh (pair_bi p) TB *
  ptable sh (pair_ak p) ka * ptable sh (pair_bk p) kb *
  peer_rep5 sh (pair_ap p) PA * peer_rep5 sh (pair_bp p) PB
  |-- @data_at_ CSh sh t_pair p * TT.
Proof.
  intros Hfc [EA [HA _]] [EB [HB _]].
  sep_apply (hs_close_dev sh (pair_a p) DA). sep_apply (hs_close_dev sh (pair_b p) DB).
  sep_apply (hs_close_itable sh (pair_ai p) TA). sep_apply (hs_close_itable sh (pair_bi p) TB).
  sep_apply (hbs_pool_take TA _ _ _ HA). Intros na ha.
  sep_apply (hbs_pool_take TB _ _ _ HB). Intros nb hb.
  sep_apply (hs_close_peer sh (pair_ap p) PA EA na ha). sep_apply (hs_close_peer sh (pair_bp p) PB EB nb hb).
  unfold ptable.
  sep_apply (@data_at_data_at_ Noise.CS sh t_ptab ka (pair_ak p)).
  sep_apply (@data_at_data_at_ Noise.CS sh t_ptab kb (pair_bk p)).
  sep_apply (hs_pair_join sh p Hfc). cancel.
Qed.
