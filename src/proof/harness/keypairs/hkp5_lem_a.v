(* law keypairs: model facts. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.keypairs.hkp5_model.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Generic list facts *)
(* ---------------------------------------------------------------------- *)

Lemma hk5a_afind_in : forall {A} (l: list (val * A)) a v, afind l a = Some v -> In (a, v) l.
Proof.
  induction l as [|[x w] l IH]; simpl; intros a v; [discriminate|].
  if_tac; intros E; [subst; left; congruence | right; auto].
Qed.

Lemma hk5a_in_afind : forall {A} (l: list (val * A)) a v, NoDup (map fst l) -> In (a, v) l -> afind l a = Some v.
Proof.
  induction l as [|[x w] l IH]; simpl; intros a v ND I; [contradiction|].
  inv ND. destruct I as [E|I].
  - inv E. if_tac; [auto | congruence].
  - if_tac; [| auto]. subst. exfalso. apply H1. apply in_map_iff. exists (a, v); auto.
Qed.

Lemma hk5a_in_map_fst : forall {A} (l: list (val * A)) a, In a (map fst l) -> exists v, afind l a = Some v.
Proof.
  induction l as [|[x w] l IH]; simpl; intros a I; [contradiction|].
  if_tac; [eauto|]. destruct I as [E|I]; [simpl in E; congruence | auto].
Qed.

Lemma hk5a_nodup_inj : forall {A B} (f: A -> B) l x y, NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; simpl; intros x y ND Ix Iy E; [contradiction|].
  inv ND. destruct Ix as [<-|Ix], Iy as [<-|Iy]; auto.
  - exfalso. apply H1. rewrite E. apply in_map; auto.
  - exfalso. apply H1. rewrite <- E. apply in_map; auto.
Qed.

Lemma hk5a_nodup_filter_map : forall (g g': val -> bool) (f: val -> val) l,
  (forall x, g x = true <-> x <> nullval) -> (forall x, g' x = true <-> x <> nullval) ->
  (forall x, In x l -> (f x = nullval <-> x = nullval)) ->
  (forall x y, In x l -> In y l -> x <> nullval -> f x = f y -> x = y) ->
  NoDup (filter g l) -> NoDup (filter g' (map f l)).
Proof.
  induction l as [|x l IH]; simpl; intros Hg Hg' Hf Hinj ND; [constructor|].
  destruct (g x) eqn:Gx.
  - assert (Nx: x <> nullval) by (apply Hg; auto).
    assert (Gfx: g' (f x) = true). { apply Hg'. intro E. apply Nx. apply Hf; auto. }
    rewrite Gfx. inv ND. constructor.
    + intro I. apply filter_In in I as [I G]. apply in_map_iff in I as (y & E & Iy).
      assert (x = y) by (apply Hinj; auto). subst y. apply H1. apply filter_In; auto.
    + apply IH; auto.
  - assert (Xn: x = nullval). { destruct (eq_dec x nullval); auto. apply Hg in n. congruence. }
    assert (Gfx: g' (f x) = false).
    { destruct (g' (f x)) eqn:E; auto. apply Hg' in E. exfalso. apply E. apply Hf; auto. }
    rewrite Gfx. apply IH; auto.
Qed.

Lemma hk5a_filter_swap : forall {A} (g: A -> bool) a b l,
  NoDup (filter g (a :: b :: l)) -> NoDup (filter g (b :: a :: l)).
Proof.
  intros. eapply Permutation_NoDup; [| exact H]. simpl.
  destruct (g a), (g b); first [apply perm_swap | apply Permutation_refl].
Qed.

Lemma hk5a_map_fst_aupd {A: Type} (l: list (val * A)) a v :
  map fst (aupd l a v) = map fst l.
Proof.
  induction l as [|[x w] l IH]; simpl; auto.
  if_tac; simpl; f_equal; auto.
Qed.

Lemma hk5a_Forall_aupd {A: Type} (Q P: val * A -> Prop) (l: list (val * A)) a v :
  NoDup (map fst l) -> Forall Q l -> (forall x, Q x -> fst x <> a -> P x) -> P (a, v) ->
  Forall P (aupd l a v).
Proof.
  induction l as [|[x w] l IH]; simpl; intros Hnd HQ HQP HP; auto.
  apply NoDup_cons_iff in Hnd as [Hnin Hnd]. apply Forall_cons_iff in HQ as [HQx HQl].
  if_tac.
  - subst. constructor; auto.
    rewrite Forall_forall in HQl |- *. intros y Hy. apply HQP; auto.
    intro E. apply Hnin. rewrite <- E. apply in_map; auto.
  - constructor; [apply HQP; auto | auto].
Qed.

(* ---------------------------------------------------------------------- *)
(* The model: nodes and keypairs                                            *)
(* ---------------------------------------------------------------------- *)

Lemma hk5a_F2_map : forall p T (ML: list (val * hk5_mk)) (KS: list (val * keypair)),
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  map (fun x => m5_kp (snd x)) ML = map fst KS.
Proof. induction 1 as [|x y l1 l2 [E _] F IH]; simpl; f_equal; auto. Qed.

Lemma hk5a_F2_in : forall p T (ML: list (val * hk5_mk)) (KS: list (val * keypair)) m M,
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  In (m, M) ML -> exists K, In (m5_kp M, K) KS /\ hk5_match p T M K.
Proof.
  intros p T ML KS m M F2. induction F2 as [|x y l1 l2 [E1 MA] F2 IH]; simpl; [contradiction|].
  intros [Ex|I].
  - subst x. destruct y as [k K]. simpl in *. subst k. exists K; auto.
  - destruct (IH I) as (K & IK & MK). exists K; auto.
Qed.

Lemma hk5a_F2_in_fst p T ML KS m M :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  afind ML m = Some M -> In (m5_kp M) (map fst KS).
Proof.
  intros AF2 Hf. apply hk5a_afind_in in Hf. destruct (hk5a_F2_in _ _ _ _ _ _ AF2 Hf) as (K & IK & _).
  apply in_map_iff. exists (m5_kp M, K); auto.
Qed.

Lemma hk5a_F2_aupd p T ML KS m M M' K' :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  NoDup (map fst KS) -> afind ML m = Some M ->
  m5_kp M' = m5_kp M -> hk5_match p T M' K' ->
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y))
    (aupd ML m M') (aupd KS (m5_kp M) K').
Proof.
  intros AF2; induction AF2 as [|[x Mx] [y Ky] ML KS [E Hm] HF IH]; simpl; intros Hnd Hf Ek HM;
    [discriminate|].
  simpl in E, Hm. apply NoDup_cons_iff in Hnd as [Hnin Hnd].
  revert Hf. if_tac; intros Hf.
  - inversion Hf; subst x Mx. rewrite if_true by auto.
    constructor; auto. simpl. split; auto. congruence.
  - if_tac.
    + exfalso. apply Hnin. rewrite H0. eapply hk5a_F2_in_fst; eauto.
    + constructor; auto.
Qed.

Lemma hk5a_cnt_in : forall R m, In m R <-> 0 < hk5_cnt R m.
Proof.
  intros R m. unfold hk5_cnt. split.
  - intros I. assert (I': In m (filter (hk5_eqb m) R)).
    { apply filter_In. split; auto. unfold hk5_eqb. destruct (eq_dec m m); congruence. }
    destruct (filter (hk5_eqb m) R) as [|x l]; [contradiction|].
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
  - intros Z. destruct (filter (hk5_eqb m) R) as [|x l] eqn:E; [rewrite Zlength_nil in Z; lia|].
    assert (I: In x (filter (hk5_eqb m) R)) by (rewrite E; left; auto).
    apply filter_In in I as [I G]. unfold hk5_eqb in G. destruct (eq_dec m x); [subst; auto | discriminate].
Qed.

(* ---------------------------------------------------------------------- *)
(* refcount_t against m_get                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hk5a_rc_range_nz r :
  r = REFCOUNT_SATURATED \/ 1 <= Int.unsigned r <= Int.max_signed -> Int.eq r Int.zero = false.
Proof.
  intros [->|B]; [reflexivity|].
  pose proof (Int.eq_spec r Int.zero) as S. destruct (Int.eq r Int.zero); auto.
  subst r. rewrite Int.unsigned_zero in B. lia.
Qed.

Lemma hk5a_rc_sat r :
  r = REFCOUNT_SATURATED \/ 1 <= Int.unsigned r <= Int.max_signed ->
  orb (rc_neg r) (rc_neg (Int.add r Int.one)) = hk5_get_sat r.
Proof.
  intros [->|B]; [reflexivity|].
  destruct (zeq (Int.unsigned r) 2147483647) as [E|N].
  - assert (r = hk5_INT_MAX) as -> by (rewrite <- (Int.repr_unsigned r), E; reflexivity). reflexivity.
  - unfold rc_neg, hk5_get_sat, Int.ltu, Int.eq.
    rewrite Int.add_unsigned, Int.unsigned_one, Int.unsigned_repr by rep_lia.
    unfold hk5_INT_MAX. rewrite hk5_sat_eq.
    rewrite !Int.unsigned_repr by rep_lia.
    repeat first [destruct zlt; try rep_lia | destruct zeq; try rep_lia]; reflexivity.
Qed.

Lemma hk5a_rc_add1 r :
  r = REFCOUNT_SATURATED \/ 1 <= Int.unsigned r <= Int.max_signed -> rc_add1 r = hk5_get_refs r.
Proof.
  intros B. unfold rc_add1, hk5_get_refs. rewrite hk5a_rc_sat by exact B. reflexivity.
Qed.

Lemma hk5a_rc_inz_warn r w :
  r = REFCOUNT_SATURATED \/ 1 <= Int.unsigned r <= Int.max_signed ->
  rc_inz_warn r w = if hk5_get_sat r then warn_bump w REFCOUNT_ADD_NOT_ZERO_OVF else w.
Proof.
  intros B. unfold rc_inz_warn. rewrite hk5a_rc_range_nz by exact B. rewrite hk5a_rc_sat by exact B.
  reflexivity.
Qed.

Lemma hk5a_warn_bump0 w0 mw w : hk5_warn_ok w0 mw w ->
  hk5_warn_ok w0 (warn_bump mw REFCOUNT_ADD_NOT_ZERO_OVF) (warn_bump w REFCOUNT_ADD_NOT_ZERO_OVF).
Proof.
  intros (L0 & Lm & Lw & EQ & Z1 & Z2 & Z4).
  unfold hk5_warn_ok, warn_bump.
  unfold REFCOUNT_ADD_NOT_ZERO_OVF, REFCOUNT_ADD_OVF, REFCOUNT_ADD_UAF, REFCOUNT_DEC_LEAK in *.
  split; [exact L0|]. split; [rewrite upd_Znth_Zlength; lia|]. split; [rewrite upd_Znth_Zlength; lia|].
  split.
  - intros i Hi. destruct (zeq i 0) as [->|Ne].
    + rewrite !upd_Znth_same by lia. rewrite EQ by lia. rewrite Int64.add_assoc. reflexivity.
    + rewrite !upd_Znth_diff by lia. apply EQ; lia.
  - split; [|split]; rewrite upd_Znth_diff by lia; assumption.
Qed.

Lemma hk5a_count_get R m M : hk5_count_ok R m M -> hk5_count_ok R m (hk5_mget M).
Proof.
  unfold hk5_count_ok, hk5_mget, m5_set_held, m5_set_refs; cbn [m5_refs m5_held].
  intros [E|[E B]].
  - left. rewrite E. reflexivity.
  - unfold hk5_get_refs. rewrite <- hk5a_rc_sat by (right; exact B).
    destruct (zeq (Int.unsigned (m5_refs M)) 2147483647) as [EM|NM].
    + assert (X: m5_refs M = hk5_INT_MAX) by (rewrite <- (Int.repr_unsigned (m5_refs M)), EM; reflexivity).
      rewrite X. left. reflexivity.
    + assert (S: orb (rc_neg (m5_refs M)) (rc_neg (Int.add (m5_refs M) Int.one)) = false).
      { unfold rc_neg, Int.ltu.
        rewrite Int.add_unsigned, Int.unsigned_one, !Int.unsigned_repr by rep_lia.
        repeat (destruct zlt; try rep_lia); reflexivity. }
      rewrite S. right.
      pose proof (Zlength_nonneg (filter (hk5_eqb m) R)). fold (hk5_cnt R m) in H.
      pose proof (Int64.unsigned_range (m5_held M)).
      rewrite Int.add_unsigned, Int.unsigned_one, Int.unsigned_repr by rep_lia.
      rewrite Int64.add_unsigned, Int64.unsigned_one, Int64.unsigned_repr by rep_lia.
      rep_lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The four facts                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_lem_a_pre : hk5_fact_pre.
Proof.
  intros p OD OH R ML KS T (F2 & ND1 & NN1 & ND2 & NN2 & FR & FC & FH & POOL).
  destruct POOL as (_ & _ & _ & _ & [idx IX] & _).
  assert (MAP := hk5a_F2_map _ _ _ _ F2).
  assert (KM: forall m M, afind ML m = Some M -> exists K, afind KS (m5_kp M) = Some K /\ hk5_match p T M K).
  { intros m M AF. apply hk5a_afind_in in AF. destruct (hk5a_F2_in _ _ _ _ _ _ F2 AF) as (K & IK & MK).
    exists K; split; auto. apply hk5a_in_afind; auto. }
  assert (SK: forall m, In m (map fst ML) ->
                hk5_slot_kp ML m <> nullval /\ In (hk5_slot_kp ML m) (map fst KS)).
  { intros m I. unfold hk5_slot_kp. destruct (eq_dec m nullval) as [->|]; [contradiction|].
    destruct (hk5a_in_map_fst _ _ I) as [M AF]. rewrite AF.
    destruct (KM _ _ AF) as (K & AK & _). apply hk5a_afind_in in AK.
    assert (IK: In (m5_kp M) (map fst KS)) by (apply in_map_iff; exists (m5_kp M, K); auto).
    split; auto. intros E; rewrite E in IK; contradiction. }
  split; [| split; [| split; [exact KM | split; [exact SK |]]]].
  - split; auto. clear - F2. induction F2 as [|x y l1 l2 [E1 MA] F2 IH]; constructor; auto.
    destruct MA as (_ & SF & _). exists (mkEntry p IDX_KEYPAIR (m5_index (snd x))). rewrite E1. split; auto.
  - exists (mkEntry p IDX_HANDSHAKE idx). unfold t_entry. rewrite IX. auto.
  - intros m1 m2 I1 [->|I2] E.
    + exfalso. destruct (SK _ I1) as [N _]. apply N. rewrite E. unfold hk5_slot_kp.
      destruct (eq_dec nullval nullval); congruence.
    + destruct (hk5a_in_map_fst _ _ I1) as [M1 A1]. destruct (hk5a_in_map_fst _ _ I2) as [M2 A2].
      unfold hk5_slot_kp in E.
      destruct (eq_dec m1 nullval) as [->|]; [contradiction|].
      destruct (eq_dec m2 nullval) as [->|]; [contradiction|].
      rewrite A1, A2 in E.
      apply hk5a_afind_in in A1. apply hk5a_afind_in in A2.
      rewrite <- MAP in ND2.
      assert (X := hk5a_nodup_inj (fun x => m5_kp (snd x)) ML _ _ ND2 A1 A2 E). congruence.
Qed.

Lemma hkp5_lem_a_slots : hk5_fact_slots.
Proof.
  intros p OD OH H P KS T (CORE & NDS & Hp & Hc & Hn).
  pose proof CORE as CORE'. destruct CORE' as (_ & _ & _ & _ & _ & FS & _).
  destruct (hkp5_lem_a_pre _ _ _ _ _ _ _ CORE) as (_ & _ & _ & SK & INJ).
  unfold slots_ok. rewrite Hp, Hc, Hn.
  unfold hk5_slots in FS. unfold hk5_nonnull, hk5_slots in NDS.
  set (ML := h5_ML H) in *. set (a := h5_sp H) in *. set (b := h5_sc H) in *. set (c := h5_sn H) in *.
  assert (F3: forall x, In x [b; a; c] -> x = nullval \/ In x (map fst ML)).
  { rewrite Forall_forall in FS. intros x I. apply FS. simpl in *; tauto. }
  assert (SN: forall x, In x [b; a; c] -> (hk5_slot_kp ML x = nullval <-> x = nullval)).
  { intros x I. destruct (F3 x I) as [->|Ix].
    - unfold hk5_slot_kp. destruct (eq_dec nullval nullval); [tauto | congruence].
    - destruct (SK x Ix) as [N _]. split; intro E; [contradiction|]. subst x; contradiction. }
  split.
  - rewrite Forall_forall. intros k I.
    replace [hk5_slot_kp ML b; hk5_slot_kp ML a; hk5_slot_kp ML c] with (map (hk5_slot_kp ML) [b; a; c])
      in I by reflexivity.
    apply in_map_iff in I as (x & <- & I). destruct (F3 x I) as [->|Ix].
    + left. unfold hk5_slot_kp. destruct (eq_dec nullval nullval); congruence.
    + right. apply SK; auto.
  - apply (hk5a_nodup_filter_map (fun x => negb (hk5_eqb x nullval)) _ (hk5_slot_kp ML) [b; a; c]).
    + intros x. unfold hk5_eqb. destruct (eq_dec x nullval); simpl; split; intros; congruence.
    + intros x. destruct (eq_dec x nullval); simpl; split; intros; congruence.
    + exact SN.
    + intros x y Ix Iy Nx E. apply INJ; auto.
      destruct (F3 x Ix); [contradiction | auto].
    + apply hk5a_filter_swap. exact NDS.
Qed.

Lemma hkp5_lem_a_perm : hk5_fact_perm.
Proof.
  intros p OD OH R R' ML KS T CNT FR' (F2 & ND1 & NN1 & ND2 & NN2 & FR & FC & FH & POOL).
  assert (NNm: forall x, In x ML -> fst x <> nullval).
  { intros x I E. apply NN1. rewrite <- E. apply in_map; auto. }
  refine (conj F2 (conj ND1 (conj NN1 (conj ND2 (conj NN2 (conj FR' (conj _ (conj _ POOL)))))))).
  - rewrite Forall_forall in FC |- *. intros x I. specialize (FC x I). unfold hk5_count_ok in *.
    rewrite <- CNT by (apply NNm; auto). exact FC.
  - rewrite Forall_forall in FH |- *. intros x I Hh. specialize (FH x I Hh).
    apply hk5a_cnt_in. rewrite <- CNT by (apply NNm; auto). apply hk5a_cnt_in. exact FH.
Qed.

Lemma hkp5_lem_a_get : hk5_fact_get.
Proof.
  intros p OD OH R ML KS T mw w0 w m M Hc Hw Hf.
  pose proof (hkp5_lem_a_pre p OD OH R ML KS T Hc) as (_ & _ & Hkp & _ & _).
  destruct (Hkp m M Hf) as (K & HK & HmK).
  destruct Hc as (HF2 & HndML & HnnML & HndKS & HnnKS & HR & Hcnt & Hhs & Hpool).
  assert (HinK: In (m5_kp M) (map fst KS)).
  { apply hk5a_afind_in in HK. apply (in_map fst) in HK. exact HK. }
  assert (Hknn: m5_kp M <> nullval) by (intro E; apply HnnKS; rewrite <- E; auto).
  assert (HinmML: In (m, M) ML) by (apply hk5a_afind_in; auto).
  assert (Hcm: hk5_count_ok R m M) by (rewrite Forall_forall in Hcnt; apply (Hcnt (m, M)); auto).
  assert (Hrng: m5_refs M = REFCOUNT_SATURATED \/ 1 <= Int.unsigned (m5_refs M) <= Int.max_signed).
  { destruct Hcm as [E|[_ E]]; auto. }
  pose proof HmK as HmK0. destruct HmK as [Hr HmK'].
  assert (Hget: kp_get (m5_kp M) KS =
    (m5_kp M, aupd KS (m5_kp M) (kp_set_refs K (hk5_get_refs (m5_refs M))))).
  { unfold kp_get. rewrite if_false by exact Hknn. rewrite HK, Hr, hk5a_rc_range_nz by exact Hrng.
    rewrite hk5a_rc_add1 by exact Hrng. reflexivity. }
  rewrite Hget; cbn [fst snd]. split; [reflexivity|]. split.
  2: { unfold kp_get_warn. rewrite if_false by exact Hknn. rewrite HK, Hr.
       rewrite hk5a_rc_inz_warn by exact Hrng. unfold hk5_get_warn.
       destruct (hk5_get_sat (m5_refs M)); [apply hk5a_warn_bump0 |]; exact Hw. }
  unfold hk5_core. rewrite !hk5a_map_fst_aupd.
  refine (conj _ (conj HndML (conj HnnML (conj HndKS (conj HnnKS (conj HR (conj _ (conj _ _)))))))).
  - apply (hk5a_F2_aupd p T ML KS m M); auto.
    unfold hk5_match in *; unfold hk5_mget, m5_set_held, m5_set_refs, kp_set_refs; cbn. tauto.
  - apply hk5a_Forall_aupd with (Q := fun x => hk5_count_ok R (fst x) (snd x)); auto.
    cbn [fst snd]. apply hk5a_count_get. exact Hcm.
  - apply hk5a_Forall_aupd with (Q := fun x => m5_hashed (snd x) = true -> In (fst x) R); auto.
    cbn [fst snd]. rewrite Forall_forall in Hhs. exact (Hhs (m, M) HinmML).
  - unfold hk5_pool in *. rewrite !hk5a_map_fst_aupd. exact Hpool.
Qed.

Lemma hkp5_lem_a : hk5_fact_pre /\ hk5_fact_slots /\ hk5_fact_perm /\ hk5_fact_get.
Proof.
  exact (conj hkp5_lem_a_pre (conj hkp5_lem_a_slots (conj hkp5_lem_a_perm hkp5_lem_a_get))).
Qed.
