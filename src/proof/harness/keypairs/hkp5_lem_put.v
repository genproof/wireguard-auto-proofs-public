(* law keypairs: model facts of the puts.  The statement is
*)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.keypairs.hkp5_model.

Local Open Scope Z_scope.

(* Adapted from the One-step unfolding that keeps eq_dec folded
   (simpl turns it into EqDec_val, which destruct (eq_dec ..) misses). *)
Ltac hlp_cbn := cbn [afind aupd adel sfind sdel saddrs vremove map fst snd hk5_remove1 In filter].
Tactic Notation "hlp_cbn" "in" hyp_list(H) :=
  cbn [afind aupd adel sfind sdel saddrs vremove map fst snd hk5_remove1 In filter] in H.

(* ---------------------------------------------------------------------- *)
(* association lists                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_lem_put_afind_in {A} (l: list (val * A)) a :
  In a (map fst l) -> exists v, afind l a = Some v.
Proof.
  induction l as [|[x w] l IH]; hlp_cbn; intros H; [contradiction|].
  destruct (eq_dec x a); [eauto|]. destruct H as [H|H]; [contradiction|auto].
Qed.

Lemma hkp5_lem_put_afind_In {A} (l: list (val * A)) a v :
  afind l a = Some v -> In (a, v) l.
Proof.
  induction l as [|[x w] l IH]; hlp_cbn; intros H; [discriminate|].
  destruct (eq_dec x a); [inversion H; subst; auto|auto].
Qed.

Lemma hkp5_lem_put_afind_nodup {A} (l: list (val * A)) x :
  NoDup (map fst l) -> In x l -> afind l (fst x) = Some (snd x).
Proof.
  induction l as [|[y w] l IH]; hlp_cbn; intros Hn Hi; [contradiction|].
  apply NoDup_cons_iff in Hn as [Hn1 Hn2].
  destruct Hi as [Hi|Hi].
  - subst; hlp_cbn. destruct (eq_dec y y); [auto|contradiction].
  - destruct (eq_dec y (fst x)).
    + subst. exfalso. apply Hn1. apply in_map. auto.
    + auto.
Qed.

Lemma hkp5_lem_put_map_fst_aupd {A} (l: list (val * A)) a v : map fst (aupd l a v) = map fst l.
Proof.
  induction l as [|[x w] l IH]; hlp_cbn; auto. destruct (eq_dec x a); hlp_cbn; f_equal; auto.
Qed.

Lemma hkp5_lem_put_Zlength_aupd {A} (l: list (val * A)) a v : Zlength (aupd l a v) = Zlength l.
Proof.
  rewrite <- (Zlength_map _ _ fst (aupd l a v)), hkp5_lem_put_map_fst_aupd, Zlength_map. auto.
Qed.

Lemma hkp5_lem_put_in_aupd {A} (l: list (val * A)) a v x :
  NoDup (map fst l) -> In x (aupd l a v) -> x = (a, v) \/ (In x l /\ fst x <> a).
Proof.
  induction l as [|[y w] l IH]; hlp_cbn; intros Hn Hi; [contradiction|].
  apply NoDup_cons_iff in Hn as [Hn1 Hn2].
  destruct (eq_dec y a).
  - subst. destruct Hi as [Hi|Hi]; [left; auto|].
    right. split; [auto|]. intros E. apply Hn1. rewrite <- E. apply in_map; auto.
  - destruct Hi as [Hi|Hi].
    + subst. right. hlp_cbn. auto.
    + destruct (IH Hn2 Hi) as [H|[H1 H2]]; auto.
Qed.

Lemma hkp5_lem_put_in_adel {A} (l: list (val * A)) a x :
  NoDup (map fst l) -> In x (adel l a) -> In x l /\ fst x <> a.
Proof.
  induction l as [|[y w] l IH]; hlp_cbn; intros Hn Hi; [contradiction|].
  apply NoDup_cons_iff in Hn as [Hn1 Hn2].
  destruct (eq_dec y a).
  - subst. split; [auto|]. intros E. apply Hn1. rewrite <- E. apply in_map; auto.
  - destruct Hi as [Hi|Hi].
    + subst. hlp_cbn. auto.
    + destruct (IH Hn2 Hi). auto.
Qed.

Lemma hkp5_lem_put_in_fst_adel {A} (l: list (val * A)) a x :
  NoDup (map fst l) -> (In x (map fst (adel l a)) <-> In x (map fst l) /\ x <> a).
Proof.
  induction l as [|[y w] l IH]; hlp_cbn; intros Hn; [tauto|].
  apply NoDup_cons_iff in Hn as [Hn1 Hn2].
  destruct (eq_dec y a).
  - subst. split.
    + intros H. split; [auto|]. intros E; subst; contradiction.
    + intros [[H|H] H']; [subst; contradiction|auto].
  - hlp_cbn. rewrite IH by auto. split.
    + intros [H|[H H']]; [subst; auto|auto].
    + intros [[H|H] H']; auto.
Qed.

Lemma hkp5_lem_put_nodup_adel {A} (l: list (val * A)) a :
  NoDup (map fst l) -> NoDup (map fst (adel l a)).
Proof.
  induction l as [|[y w] l IH]; hlp_cbn; intros Hn; auto.
  pose proof Hn as Hn0. apply NoDup_cons_iff in Hn as [Hn1 Hn2].
  destruct (eq_dec y a); auto.
  hlp_cbn. constructor; auto. rewrite hkp5_lem_put_in_fst_adel by auto. tauto.
Qed.

Lemma hkp5_lem_put_Zlength_adel {A} (l: list (val * A)) a :
  In a (map fst l) -> Zlength (adel l a) = Zlength l - 1.
Proof.
  induction l as [|[y w] l IH]; hlp_cbn; intros H; [contradiction|].
  destruct (eq_dec y a).
  - rewrite Zlength_cons. lia.
  - destruct H as [H|H]; [contradiction|]. rewrite !Zlength_cons, IH by auto. lia.
Qed.

Lemma hkp5_lem_put_aupd_aupd {A} (l: list (val * A)) a v w : aupd (aupd l a v) a w = aupd l a w.
Proof.
  induction l as [|[x u] l IH]; hlp_cbn; auto.
  destruct (eq_dec x a); hlp_cbn; rewrite ?IH; destruct (eq_dec x a); try contradiction; auto.
Qed.

Lemma hkp5_lem_put_adel_aupd {A} (l: list (val * A)) a v : adel (aupd l a v) a = adel l a.
Proof.
  induction l as [|[x u] l IH]; hlp_cbn; auto.
  destruct (eq_dec x a); hlp_cbn; rewrite ?IH; destruct (eq_dec x a); try contradiction; auto.
Qed.

Lemma hkp5_lem_put_afind_aupd {A} (l: list (val * A)) a v M :
  afind l a = Some M -> afind (aupd l a v) a = Some v.
Proof.
  induction l as [|[x u] l IH]; hlp_cbn; intros H; [discriminate|].
  destruct (eq_dec x a); hlp_cbn; destruct (eq_dec x a); try contradiction; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* aligned lists                                                            *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_lem_put_F2_strengthen {A B} (P Q: A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> (forall x y, In x l1 -> P x y -> Q x y) -> Forall2 Q l1 l2.
Proof.
  induction 1 as [|x y l1 l2 HP H IH]; intros HQ; constructor.
  - apply HQ; hlp_cbn; auto.
  - apply IH. intros; apply HQ; hlp_cbn; auto.
Qed.

Lemma hkp5_lem_put_F2_out {A B} (P Q: (val * A) -> (val * B) -> Prop) l1 l2 a b :
  Forall2 (fun x y => P x y /\ (fst x = a <-> fst y = b)) l1 l2 -> ~ In a (map fst l1) ->
  (forall x y, P x y -> fst x <> a -> fst y <> b -> Q x y) -> Forall2 Q l1 l2.
Proof.
  induction 1 as [|x y l1 l2 [HP Hab] H IH]; intros Hn HQ; constructor.
  - hlp_cbn in Hn. apply HQ; auto; tauto.
  - apply IH; auto. hlp_cbn in Hn; tauto.
Qed.

Lemma hkp5_lem_put_F2_adel {A B} (P Q: (val * A) -> (val * B) -> Prop) l1 l2 a b :
  Forall2 (fun x y => P x y /\ (fst x = a <-> fst y = b)) l1 l2 -> NoDup (map fst l1) ->
  (forall x y, P x y -> fst x <> a -> fst y <> b -> Q x y) ->
  Forall2 Q (adel l1 a) (adel l2 b).
Proof.
  induction 1 as [|[x v] [y w] l1 l2 [HP Hab] H IH]; intros Hn HQ; hlp_cbn; [constructor|].
  apply NoDup_cons_iff in Hn as [Hn1 Hn2]. hlp_cbn in Hab; hlp_cbn in Hn1.
  destruct (eq_dec x a) as [Ea|Ea], (eq_dec y b) as [Eb|Eb].
  - rewrite Ea in Hn1. apply (hkp5_lem_put_F2_out P Q l1 l2 a b); auto.
  - exfalso; tauto.
  - exfalso; tauto.
  - constructor; [apply HQ; hlp_cbn; auto|auto].
Qed.

Lemma hkp5_lem_put_F2_aupd {A B} (P Q: (val * A) -> (val * B) -> Prop) l1 l2 a b v w :
  Forall2 (fun x y => P x y /\ (fst x = a <-> fst y = b)) l1 l2 -> NoDup (map fst l1) ->
  (forall x y, P x y -> fst x <> a -> fst y <> b -> Q x y) -> Q (a, v) (b, w) ->
  Forall2 Q (aupd l1 a v) (aupd l2 b w).
Proof.
  induction 1 as [|[x v0] [y w0] l1 l2 [HP Hab] H IH]; intros Hn HQ Hab'; hlp_cbn; [constructor|].
  apply NoDup_cons_iff in Hn as [Hn1 Hn2]. hlp_cbn in Hab; hlp_cbn in Hn1.
  destruct (eq_dec x a) as [Ea|Ea], (eq_dec y b) as [Eb|Eb].
  - subst x y. constructor; auto. apply (hkp5_lem_put_F2_out P Q l1 l2 a b); auto.
  - exfalso; tauto.
  - exfalso; tauto.
  - constructor; [apply HQ; hlp_cbn; auto|auto].
Qed.

(* the node <-> keypair alignment of the core *)
Lemma hkp5_lem_put_F2_in p T (ML: list (val * hk5_mk)) (KS: list (val * keypair)) m M :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  In (m, M) ML -> exists K, In (m5_kp M, K) KS /\ hk5_match p T M K.
Proof.
  intros F2. induction F2 as [|x y l1 l2 [E1 MA] F2 IH]; hlp_cbn; [contradiction|].
  intros [Ex|I].
  - subst x. destruct y as [k K]. hlp_cbn in E1. hlp_cbn in MA. subst k. exists K; auto.
  - destruct (IH I) as (K & IK & MK). exists K; auto.
Qed.

Lemma hkp5_lem_put_F2_iff p T (ML: list (val * hk5_mk)) (KS: list (val * keypair)) m M :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  NoDup (map fst ML) -> NoDup (map fst KS) -> afind ML m = Some M ->
  Forall2 (fun x y => (fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) /\
                      (fst x = m <-> fst y = m5_kp M)) ML KS.
Proof.
  intros F2. induction F2 as [|[x X] [y Y] l1 l2 [E1 MA] F2 IH]; hlp_cbn; intros N1 N2 HM; [discriminate|].
  apply NoDup_cons_iff in N1 as [N1a N1b]. apply NoDup_cons_iff in N2 as [N2a N2b].
  hlp_cbn in E1. subst y.
  destruct (eq_dec x m) as [Ex|Ex].
  - inversion HM; subst x X. constructor; [split; [split; auto|]; hlp_cbn; tauto|].
    clear IH. induction F2 as [|[x' X'] [y' Y'] l1 l2 [E1' MA'] F2' IH']; constructor.
    + split; [split; auto|]. hlp_cbn. hlp_cbn in N1a. hlp_cbn in N2a. hlp_cbn in E1'.
      split; intros E; exfalso; [apply N1a|apply N2a]; left; congruence.
    + hlp_cbn in N1a. hlp_cbn in N2a. apply IH'; auto.
      * apply NoDup_cons_iff in N1b; tauto.
      * apply NoDup_cons_iff in N2b; tauto.
  - constructor; [|apply IH; auto].
    split; [split; auto|]. hlp_cbn. split; intros E; [contradiction|exfalso].
    apply hkp5_lem_put_afind_In in HM.
    destruct (hkp5_lem_put_F2_in p T l1 l2 m M F2 HM) as (K & IK & _).
    apply N2a. rewrite E. apply (in_map fst _ _ IK).
Qed.

(* ---------------------------------------------------------------------- *)
(* reference counts                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_lem_put_cnt_cons m x R :
  hk5_cnt (x :: R) m = (if eq_dec m x then 1 else 0) + hk5_cnt R m.
Proof.
  unfold hk5_cnt, hk5_eqb; hlp_cbn. destruct (eq_dec m x); hlp_cbn; rewrite ?Zlength_cons; lia.
Qed.

Lemma hkp5_lem_put_cnt_nonneg m R : 0 <= hk5_cnt R m.
Proof. unfold hk5_cnt. apply Zlength_nonneg. Qed.

Lemma hkp5_lem_put_cnt_pos m R : In m R -> 1 <= hk5_cnt R m.
Proof.
  induction R as [|x R IH]; hlp_cbn; intros H; [contradiction|].
  rewrite hkp5_lem_put_cnt_cons. pose proof (hkp5_lem_put_cnt_nonneg m R).
  destruct (eq_dec m x); [lia|]. destruct H as [H|H]; [subst; contradiction|]. specialize (IH H); lia.
Qed.

Lemma hkp5_lem_put_cnt_rm_same m R : In m R -> hk5_cnt (hk5_remove1 m R) m = hk5_cnt R m - 1.
Proof.
  induction R as [|x R IH]; hlp_cbn; intros H; [contradiction|].
  destruct (eq_dec x m).
  - subst. rewrite hkp5_lem_put_cnt_cons. destruct (eq_dec m m); [lia|contradiction].
  - rewrite !hkp5_lem_put_cnt_cons. destruct (eq_dec m x); [subst; contradiction|].
    destruct H as [H|H]; [subst; contradiction|]. rewrite IH; auto; lia.
Qed.

Lemma hkp5_lem_put_cnt_rm_other m x R : x <> m -> hk5_cnt (hk5_remove1 m R) x = hk5_cnt R x.
Proof.
  induction R as [|y R IH]; hlp_cbn; intros H; auto.
  destruct (eq_dec y m).
  - subst. rewrite hkp5_lem_put_cnt_cons. destruct (eq_dec x m); [contradiction|lia].
  - rewrite !hkp5_lem_put_cnt_cons, IH; auto.
Qed.

Lemma hkp5_lem_put_in_rm m x R : In x (hk5_remove1 m R) -> In x R.
Proof.
  induction R as [|y R IH]; hlp_cbn; auto. destruct (eq_dec y m); hlp_cbn; intuition.
Qed.

Lemma hkp5_lem_put_in_rm_other m x R : x <> m -> In x R -> In x (hk5_remove1 m R).
Proof.
  induction R as [|y R IH]; hlp_cbn; intros Hx H; auto.
  destruct (eq_dec y m).
  - subst. destruct H as [H|H]; [subst; contradiction|auto].
  - hlp_cbn. destruct H as [H|H]; auto.
Qed.

Lemma hkp5_lem_put_cnt_zero m R : hk5_cnt R m = 0 -> ~ In m R.
Proof.
  intros H I. pose proof (hkp5_lem_put_cnt_pos m R I). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* the table                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_lem_put_sfind_sdel {A} (D: list (val * share * A)) k a :
  a <> k -> sfind (sdel D k) a = sfind D a.
Proof.
  induction D as [|[[x sh] w] D IH]; hlp_cbn; intros H; auto.
  destruct (eq_dec x k).
  - subst. destruct (eq_dec k a); [subst; contradiction|auto].
  - hlp_cbn. destruct (eq_dec x a); auto.
Qed.

Lemma hkp5_lem_put_saddrs_sdel {A} (D: list (val * share * A)) k a :
  NoDup (saddrs D) -> (In a (saddrs (sdel D k)) <-> In a (saddrs D) /\ a <> k).
Proof.
  induction D as [|[[x sh] w] D IH]; hlp_cbn; intros Hn; [tauto|].
  apply NoDup_cons_iff in Hn as [Hn1 Hn2].
  destruct (eq_dec x k).
  - subst. split.
    + intros H. split; [auto|]. intros E; subst; contradiction.
    + intros [[H|H] H']; [subst; contradiction|auto].
  - hlp_cbn. rewrite IH by auto. split.
    + intros [H|[H H']]; [subst; auto|auto].
    + intros [[H|H] H']; auto.
Qed.

Lemma hkp5_lem_put_nodup_sdel {A} (D: list (val * share * A)) k :
  NoDup (saddrs D) -> NoDup (saddrs (sdel D k)).
Proof.
  induction D as [|[[x sh] w] D IH]; hlp_cbn; intros Hn; auto.
  pose proof Hn as Hn0. apply NoDup_cons_iff in Hn as [Hn1 Hn2].
  destruct (eq_dec x k); auto.
  hlp_cbn. constructor; [|exact (IH Hn2)].
  change (~ In x (saddrs (sdel D k))). rewrite hkp5_lem_put_saddrs_sdel by exact Hn2.
  intros [H _]. exact (Hn1 H).
Qed.

Lemma hkp5_lem_put_Forall_sdel {A} (P: val * share * A -> Prop) (D: list (val * share * A)) k :
  Forall P D -> Forall P (sdel D k).
Proof.
  induction D as [|[[x sh] w] D IH]; hlp_cbn; intros H; auto.
  inversion H; subst. destruct (eq_dec x k); auto.
Qed.

Lemma hkp5_lem_put_in_vremove k a L : In a (vremove k L) <-> In a L /\ a <> k.
Proof.
  induction L as [|x L IH]; hlp_cbn; [tauto|].
  destruct (eq_dec x k).
  - subst. rewrite IH. split; [tauto|]. intros [[H|H] H']; [subst; contradiction|auto].
  - hlp_cbn. rewrite IH. split.
    + intros [H|[H H']]; [subst; auto|auto].
    + intros [[H|H] H']; auto.
Qed.

Lemma hkp5_lem_put_vin_vremove k a L : a <> k -> vin a (vremove k L) = vin a L.
Proof.
  intros H; unfold vin.
  destruct (in_dec eq_dec a (vremove k L)) as [H1|H1], (in_dec eq_dec a L) as [H2|H2]; auto;
    rewrite hkp5_lem_put_in_vremove in H1; tauto.
Qed.

Lemma hkp5_lem_put_vin_vremove_same k L : vin k (vremove k L) = false.
Proof.
  unfold vin. destruct (in_dec eq_dec k (vremove k L)) as [H|H]; auto.
  rewrite hkp5_lem_put_in_vremove in H; tauto.
Qed.

Lemma hkp5_lem_put_vremove_idem k L : vremove k (vremove k L) = vremove k L.
Proof.
  induction L as [|x L IH]; hlp_cbn; auto.
  destruct (eq_dec x k); auto. hlp_cbn. destruct (eq_dec x k); [contradiction|]. f_equal; auto.
Qed.

Lemma hkp5_lem_put_nodup_map_vremove {B} (f: val -> B) k L :
  NoDup (map f L) -> NoDup (map f (vremove k L)).
Proof.
  induction L as [|x L IH]; hlp_cbn; intros Hn; auto.
  apply NoDup_cons_iff in Hn as [Hn1 Hn2].
  destruct (eq_dec x k); auto.
  hlp_cbn. constructor; auto. intros Hi. apply Hn1.
  apply in_map_iff in Hi as (y & Hy & Hi). apply hkp5_lem_put_in_vremove in Hi as [Hi _].
  rewrite <- Hy. apply in_map; auto.
Qed.

Lemma hkp5_lem_put_nodup_vremove k L : NoDup L -> NoDup (vremove k L).
Proof.
  intros H. rewrite <- (map_id (vremove k L)). apply hkp5_lem_put_nodup_map_vremove. rewrite map_id. auto.
Qed.

Lemma hkp5_lem_put_in_saddrs {A} (D: list (val * share * A)) a sh E : In (a, sh, E) D -> In a (saddrs D).
Proof. intros H. exact (in_map (fun '(x, _, _) => x) D (a, sh, E) H). Qed.

Lemma hkp5_lem_put_match_transfer p T T' M K :
  hk5_match p T M K ->
  sfind (t_D T') (m5_kp M) = sfind (t_D T) (m5_kp M) ->
  vin (m5_kp M) (t_L T') = vin (m5_kp M) (t_L T) ->
  hk5_match p T' M K.
Proof.
  unfold hk5_match. intros (H1 & H2 & H3 & H4) E1 E2. rewrite E1, E2. auto.
Qed.

Lemma hkp5_lem_put_t_free_remove T k : t_free (t_remove T k) k = t_free T k.
Proof. unfold t_free, t_remove. cbn [t_D t_L]. rewrite hkp5_lem_put_vremove_idem. reflexivity. Qed.

Lemma hkp5_lem_put_wf_remove T k : itable_wf T -> itable_wf (t_remove T k).
Proof.
  unfold itable_wf, t_remove. cbn [t_D t_L]. intros (H1 & H2 & H3 & H4).
  refine (conj (hkp5_lem_put_nodup_vremove k _ H1) (conj _ (conj H3 H4))).
  intros a Ha. apply hkp5_lem_put_in_vremove in Ha as [Ha _]. auto.
Qed.

Lemma hkp5_lem_put_ind_remove T k :
  NoDup (t_indices T (t_L T)) -> NoDup (t_indices (t_remove T k) (t_L (t_remove T k))).
Proof.
  unfold t_indices, t_entry, t_remove. cbn [t_D t_L]. apply hkp5_lem_put_nodup_map_vremove.
Qed.

Lemma hkp5_lem_put_match_set p T T' M K M' r :
  hk5_match p T M K -> t_D T' = t_D T -> vin (m5_kp M) (t_L T') = m5_hashed M' ->
  M' = mkMK5 (m5_kp M) r (m5_held M') (m5_hashed M') (m5_index M) (m5_send M) (m5_recv M) (m5_sv M) (m5_rv M)
             (m5_init M) (m5_rindex M) (m5_birth M) (m5_id M) (m5_scnt M) (m5_rcnt M) ->
  hk5_match p T' M' (kp_set_refs K r).
Proof.
  unfold hk5_match. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) ED Eb EM.
  rewrite EM.
  cbn [m5_kp m5_refs m5_hashed m5_index m5_send m5_recv m5_sv m5_rv m5_init m5_rindex m5_birth m5_id m5_scnt
       m5_rcnt kp_set_refs kp_refs kp_send kp_recv kp_init kp_rindex kp_id kp_scounter kp_rcounter].
  rewrite ED. auto 20.
Qed.

(* ---------------------------------------------------------------------- *)
(* the core after an update in place / a deletion of node m                 *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_lem_put_upd p OD OH R R' ML KS T T' m M M' K' :
  hk5_core p OD OH R ML KS T ->
  afind ML m = Some M ->
  m5_kp M' = m5_kp M -> hk5_match p T' M' K' ->
  t_D T' = t_D T -> (forall a, a <> m5_kp M -> vin a (t_L T') = vin a (t_L T)) ->
  NoDup (t_indices T' (t_L T')) -> itable_wf T' ->
  (forall x, x <> m -> hk5_cnt R' x = hk5_cnt R x) ->
  (forall x, In x R' -> In x R) ->
  (forall x, x <> m -> In x R -> In x R') ->
  hk5_count_ok R' m M' -> (m5_hashed M' = true -> In m R') ->
  hk5_core p OD OH R' (aupd ML m M') (aupd KS (m5_kp M) K') T'.
Proof.
  intros Hc HM HkM' HmK' HTD HTv HTI HTwf Hcnt' HR'1 HR'2 HcM' HhM'.
  pose proof Hc as (HF2 & HnML & HzML & HnKS & HzKS & HR & Hcnt & Hhash & Hpool).
  destruct Hpool as (HD & Hhs1 & Hhs2 & HKO & Hhs & HOD & HnI & Hwf).
  assert (HkKS: In (m5_kp M) (map fst KS)).
  { destruct (hkp5_lem_put_F2_in p T ML KS m M HF2 (hkp5_lem_put_afind_In _ _ _ HM)) as (K & IK & _).
    exact (in_map fst _ _ IK). }
  pose proof (hkp5_lem_put_F2_iff p T ML KS m M HF2 HnML HnKS HM) as HF2a.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - apply (hkp5_lem_put_F2_aupd _ _ ML KS m (m5_kp M) _ _ HF2a HnML).
    + intros x y [Hy Hxy] Hx Hy'. split; auto.
      apply (hkp5_lem_put_match_transfer p T); auto.
      * rewrite HTD; auto.
      * apply HTv. congruence.
    + cbn [fst snd]. split; auto.
  - rewrite hkp5_lem_put_map_fst_aupd; auto.
  - rewrite hkp5_lem_put_map_fst_aupd; auto.
  - rewrite hkp5_lem_put_map_fst_aupd; auto.
  - rewrite hkp5_lem_put_map_fst_aupd; auto.
  - rewrite Forall_forall in HR |- *. intros x Hx. rewrite hkp5_lem_put_map_fst_aupd. auto.
  - rewrite Forall_forall in Hcnt |- *. intros x Hx.
    apply (hkp5_lem_put_in_aupd _ _ _ _ HnML) in Hx as [Hx|[Hx Hx']].
    + subst x. exact HcM'.
    + unfold hk5_count_ok. rewrite Hcnt' by auto. apply Hcnt; auto.
  - rewrite Forall_forall in Hhash |- *. intros x Hx.
    apply (hkp5_lem_put_in_aupd _ _ _ _ HnML) in Hx as [Hx|[Hx Hx']].
    + subst x. exact HhM'.
    + intros E. apply HR'2; auto.
  - refine (conj _ (conj _ (conj Hhs2 (conj _ (conj _ (conj _ (conj HTI HTwf))))))).
    + intros a. rewrite HTD, hkp5_lem_put_map_fst_aupd. apply HD.
    + rewrite hkp5_lem_put_map_fst_aupd; auto.
    + rewrite hkp5_lem_put_map_fst_aupd; auto.
    + rewrite HTD; auto.
    + rewrite Forall_forall in HOD |- *. intros [[a sh] E] HaOD. specialize (HOD _ HaOD).
      cbv beta iota in HOD |- *. destruct HOD as [H1 H2]. rewrite HTD, HTv; auto.
      intros Ea. subst a. apply (HKO (m5_kp M) HkKS). apply (hkp5_lem_put_in_saddrs OD _ sh E HaOD).
Qed.

Lemma hkp5_lem_put_del p OD OH R R' ML KS T m M :
  hk5_core p OD OH R ML KS T ->
  afind ML m = Some M ->
  (forall x, x <> m -> hk5_cnt R' x = hk5_cnt R x) ->
  (forall x, In x R' -> In x R) -> ~ In m R' ->
  (forall x, x <> m -> In x R -> In x R') ->
  hk5_core p OD OH R' (adel ML m) (adel KS (m5_kp M)) (t_free T (m5_kp M)).
Proof.
  intros Hc HM Hcnt' HR'1 HmR' HR'2.
  pose proof Hc as (HF2 & HnML & HzML & HnKS & HzKS & HR & Hcnt & Hhash & Hpool).
  destruct Hpool as (HD & Hhs1 & Hhs2 & HKO & Hhs & HOD & HnI & Hwf).
  assert (HkKS: In (m5_kp M) (map fst KS)).
  { destruct (hkp5_lem_put_F2_in p T ML KS m M HF2 (hkp5_lem_put_afind_In _ _ _ HM)) as (K & IK & _).
    exact (in_map fst _ _ IK). }
  pose proof (hkp5_lem_put_F2_iff p T ML KS m M HF2 HnML HnKS HM) as HF2a.
  set (k := m5_kp M) in *.
  assert (Hhsk: hs_addr p <> k). { intros E. apply Hhs1. rewrite E. auto. }
  assert (HODk: forall a, In a (saddrs OD) -> a <> k). { intros a Ha E. subst a. exact (HKO k HkKS Ha). }
  destruct Hwf as (HwL & Hwincl & HwD & Hwsh).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - apply (hkp5_lem_put_F2_adel _ _ ML KS m k HF2a HnML).
    intros x y [Hy Hxy] Hx Hy'. split; auto.
    apply (hkp5_lem_put_match_transfer p T); auto.
    + cbn [t_free t_D]. apply hkp5_lem_put_sfind_sdel. congruence.
    + cbn [t_free t_L]. apply hkp5_lem_put_vin_vremove. congruence.
  - apply hkp5_lem_put_nodup_adel; auto.
  - rewrite hkp5_lem_put_in_fst_adel by auto. tauto.
  - apply hkp5_lem_put_nodup_adel; auto.
  - rewrite hkp5_lem_put_in_fst_adel by auto. tauto.
  - rewrite Forall_forall in HR |- *. intros x Hx.
    destruct (HR x (HR'1 _ Hx)) as [Hx0|Hx0]; [left; auto|right].
    rewrite hkp5_lem_put_in_fst_adel by auto. split; auto. intros E; subst x; contradiction.
  - rewrite Forall_forall in Hcnt |- *. intros x Hx.
    apply (hkp5_lem_put_in_adel _ _ _ HnML) in Hx as [Hx Hx'].
    unfold hk5_count_ok. rewrite Hcnt' by auto. apply Hcnt; auto.
  - rewrite Forall_forall in Hhash |- *. intros x Hx.
    apply (hkp5_lem_put_in_adel _ _ _ HnML) in Hx as [Hx Hx'].
    intros E. apply HR'2; auto.
  - refine (conj _ (conj _ (conj Hhs2 (conj _ (conj _ (conj _ (conj _ _))))))).
    + intros a. cbn [t_free t_D]. rewrite hkp5_lem_put_saddrs_sdel by auto.
      rewrite HD. rewrite hkp5_lem_put_in_fst_adel by auto.
      split.
      * intros [[Ha|[Ha|Ha]] Hak]; auto.
      * intros [Ha|[[Ha Hak]|Ha]]; split; auto.
        -- subst a. auto.
    + rewrite hkp5_lem_put_in_fst_adel by auto. tauto.
    + intros a Ha. rewrite hkp5_lem_put_in_fst_adel in Ha by auto. apply HKO; tauto.
    + destruct Hhs as [idx Hidx]. exists idx. cbn [t_free t_D].
      rewrite hkp5_lem_put_sfind_sdel; auto.
    + rewrite Forall_forall in HOD |- *. intros [[a sh] E] HaOD. specialize (HOD _ HaOD).
      cbv beta iota in HOD |- *. destruct HOD as [H1 H2].
      assert (Hak: a <> k) by (apply HODk; apply (hkp5_lem_put_in_saddrs OD _ sh E HaOD)).
      cbn [t_free t_D t_L]. rewrite hkp5_lem_put_sfind_sdel, hkp5_lem_put_vin_vremove; auto.
    + cbn [t_free t_L].
      assert (E: t_indices (t_free T k) (vremove k (t_L T)) = t_indices T (vremove k (t_L T))).
      { unfold t_indices. apply map_ext_in. intros a Ha. apply hkp5_lem_put_in_vremove in Ha as [_ Ha].
        unfold t_entry. cbn [t_free t_D]. rewrite hkp5_lem_put_sfind_sdel; auto. }
      rewrite E. unfold t_indices in HnI |- *. apply hkp5_lem_put_nodup_map_vremove; auto.
    + unfold itable_wf. cbn [t_free t_D t_L].
      refine (conj (hkp5_lem_put_nodup_vremove k _ HwL) (conj _ (conj (hkp5_lem_put_nodup_sdel _ k HwD)
                    (hkp5_lem_put_Forall_sdel _ _ k Hwsh)))).
      intros a Ha. apply hkp5_lem_put_in_vremove in Ha as [Ha Hak].
      rewrite hkp5_lem_put_saddrs_sdel by auto. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* warnings and counts                                                      *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_lem_put_sub1_sat : rc_sub1 REFCOUNT_SATURATED = REFCOUNT_SATURATED.
Proof. reflexivity. Qed.

Lemma hkp5_lem_put_dec_sat w : rc_dec_warn REFCOUNT_SATURATED w = warn_bump w REFCOUNT_SUB_UAF.
Proof. reflexivity. Qed.

Lemma hkp5_lem_put_warn_bump w0 mw w :
  hk5_warn_ok w0 mw w -> hk5_warn_ok w0 (warn_bump mw REFCOUNT_SUB_UAF) (warn_bump w REFCOUNT_SUB_UAF).
Proof.
  unfold hk5_warn_ok, warn_bump, REFCOUNT_SUB_UAF, REFCOUNT_ADD_OVF, REFCOUNT_ADD_UAF, REFCOUNT_DEC_LEAK.
  intros (L0 & L1 & L2 & HZ & H1 & H2 & H4).
  refine (conj L0 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - rewrite upd_Znth_Zlength by lia. auto.
  - rewrite upd_Znth_Zlength by lia. auto.
  - intros i Hi. destruct (Z.eq_dec i 3) as [->|Hne].
    + rewrite !upd_Znth_same by lia. rewrite (HZ 3) by lia. rewrite Int64.add_assoc. reflexivity.
    + rewrite !upd_Znth_diff by lia. auto.
  - rewrite upd_Znth_diff by lia. auto.
  - rewrite upd_Znth_diff by lia. auto.
  - rewrite upd_Znth_diff by lia. auto.
Qed.

Lemma hkp5_lem_put_sub_one (r: int) : 1 <= Int.unsigned r -> Int.unsigned (Int.sub r Int.one) = Int.unsigned r - 1.
Proof.
  intros H. unfold Int.sub. rewrite Int.unsigned_one. pose proof (Int.unsigned_range_2 r).
  rewrite Int.unsigned_repr; rep_lia.
Qed.

Lemma hkp5_lem_put_sub_one64 (h: int64) : 0 < Int64.unsigned h ->
  Int64.unsigned (Int64.sub h Int64.one) = Int64.unsigned h - 1.
Proof.
  intros H. unfold Int64.sub. rewrite Int64.unsigned_one. pose proof (Int64.unsigned_range_2 h).
  rewrite Int64.unsigned_repr; rep_lia.
Qed.

Ltac hlp_proj := cbn [m5_kp m5_refs m5_held m5_hashed m5_index m5_send m5_recv m5_sv m5_rv m5_init m5_rindex
  m5_birth m5_id m5_scnt m5_rcnt m5_unhash m5_set_refs m5_set_held kp_set_refs kp_refs].

(* ---------------------------------------------------------------------- *)
(* the facts                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_lem_put_fact_put : hk5_fact_put.
Proof.
  intros p OD OH R ML KS T S fr mw w0 w m Hc Hw HmR Hm.
  pose proof Hc as (HF2 & HnML & HzML & HnKS & HzKS & HR & Hcnt & Hhash & Hpool).
  assert (HmML: In m (map fst ML)).
  { rewrite Forall_forall in HR. destruct (HR m HmR); [contradiction|auto]. }
  destruct (hkp5_lem_put_afind_in ML m HmML) as [M HM].
  destruct (hkp5_lem_put_F2_in p T ML KS m M HF2 (hkp5_lem_put_afind_In _ _ _ HM)) as (K & IK & HmK).
  assert (HK: afind KS (m5_kp M) = Some K) by exact (hkp5_lem_put_afind_nodup KS (m5_kp M, K) HnKS IK).
  assert (Hk: hk5_slot_kp ML m = m5_kp M).
  { unfold hk5_slot_kp. rewrite HM. destruct (eq_dec m nullval); [contradiction|auto]. }
  assert (Hknz: m5_kp M <> nullval). { intros E. apply HzKS. rewrite <- E. exact (in_map fst _ _ IK). }
  pose proof HmK as (HKr & HKD & HKv & _).
  rewrite Hk.
  unfold hk5_put, kp_put, kp_put_warn. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec m nullval); [contradiction|].
  destruct (eq_dec (m5_kp M) nullval); [contradiction|].
  rewrite HM, HK, HKr.
  destruct Hpool as (_ & _ & _ & _ & _ & _ & HnI & Hwf).
  destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED) eqn:Hsat.
  - (* saturated: the count stays, a warning on both sides *)
    apply Int.same_if_eq in Hsat. rewrite Hsat, hkp5_lem_put_sub1_sat, hkp5_lem_put_dec_sat.
    change (Int.eq REFCOUNT_SATURATED Int.zero) with false. cbv beta iota zeta. cbn [kw_KS kw_T kw_S].
    refine (conj _ (conj (hkp5_lem_put_warn_bump _ _ _ Hw)
                         (or_introl (conj eq_refl (conj eq_refl (hkp5_lem_put_Zlength_aupd _ _ _)))))).
    apply (hkp5_lem_put_upd p OD OH R (hk5_remove1 m R) ML KS T (t_remove T (m5_kp M)) m M (m5_unhash M)
             (kp_set_refs K REFCOUNT_SATURATED) Hc HM eq_refl).
    + apply (hkp5_lem_put_match_set p T (t_remove T (m5_kp M)) M K _ REFCOUNT_SATURATED HmK eq_refl).
      * cbn [t_remove t_L m5_unhash m5_hashed]. apply hkp5_lem_put_vin_vremove_same.
      * unfold m5_unhash. rewrite Hsat. reflexivity.
    + reflexivity.
    + intros a Ha. apply hkp5_lem_put_vin_vremove; auto.
    + apply hkp5_lem_put_ind_remove; auto.
    + apply hkp5_lem_put_wf_remove; auto.
    + intros x Hx. apply hkp5_lem_put_cnt_rm_other; auto.
    + intros x Hx. eapply hkp5_lem_put_in_rm; eauto.
    + intros x Hx Hx'. apply hkp5_lem_put_in_rm_other; auto.
    + left. exact Hsat.
    + cbn [m5_unhash m5_hashed]. discriminate.
  - (* below saturation: -1, no warning *)
    assert (HcM: Int.unsigned (m5_refs M) = hk5_cnt R m + Int64.unsigned (m5_held M) /\
                 1 <= Int.unsigned (m5_refs M) <= Int.max_signed).
    { rewrite Forall_forall in Hcnt. destruct (Hcnt (m, M) (hkp5_lem_put_afind_In _ _ _ HM)) as [E|E];
        [|exact E].
      cbn [snd] in E. rewrite E, Int.eq_true in Hsat. discriminate. }
    pose proof (hkp5_lem_put_cnt_pos m R HmR) as Hc1. pose proof (Int64.unsigned_range (m5_held M)) as Hh.
    rewrite rc_sub1_small by rep_lia. rewrite rc_dec_warn_small by rep_lia.
    pose proof (hkp5_lem_put_sub_one (m5_refs M) (proj1 (proj2 HcM))) as Hr.
    destruct (Int.eq (Int.sub (m5_refs M) Int.one) Int.zero) eqn:Hz; cbv beta iota zeta; cbn [kw_KS kw_T kw_S].
    + (* the last reference: freed on both sides *)
      apply Int.same_if_eq in Hz. rewrite Hz, Int.unsigned_zero in Hr.
      assert (Hc2: hk5_cnt R m = 1) by lia.
      assert (HmR': ~ In m (hk5_remove1 m R)).
      { apply hkp5_lem_put_cnt_zero. rewrite hkp5_lem_put_cnt_rm_same; auto; lia. }
      rewrite hkp5_lem_put_t_free_remove.
      refine (conj _ (conj Hw (or_intror (conj eq_refl (conj eq_refl
                (conj (hkp5_lem_put_Zlength_adel _ _ HmML) (conj _ HmR'))))))).
      * apply (hkp5_lem_put_del p OD OH R (hk5_remove1 m R) ML KS T m M Hc HM).
        -- intros x Hx. apply hkp5_lem_put_cnt_rm_other; auto.
        -- intros x Hx. eapply hkp5_lem_put_in_rm; eauto.
        -- exact HmR'.
        -- intros x Hx Hx'. apply hkp5_lem_put_in_rm_other; auto.
      * rewrite hkp5_lem_put_in_fst_adel by auto. tauto.
    + (* still referenced *)
      assert (Hz': Int.sub (m5_refs M) Int.one <> Int.zero).
      { intros E. rewrite E, Int.eq_true in Hz. discriminate. }
      assert (Hr1: 1 <= Int.unsigned (Int.sub (m5_refs M) Int.one)).
      { destruct (zeq (Int.unsigned (Int.sub (m5_refs M) Int.one)) 0) as [E|E]; [|rep_lia].
        exfalso. apply Hz'. rewrite <- (Int.repr_unsigned (Int.sub _ _)), E. reflexivity. }
      refine (conj _ (conj Hw (or_introl (conj eq_refl (conj eq_refl (hkp5_lem_put_Zlength_aupd _ _ _)))))).
      apply (hkp5_lem_put_upd p OD OH R (hk5_remove1 m R) ML KS T (t_remove T (m5_kp M)) m M
               (m5_set_refs (m5_unhash M) (Int.sub (m5_refs M) Int.one))
               (kp_set_refs K (Int.sub (m5_refs M) Int.one)) Hc HM eq_refl).
      * apply (hkp5_lem_put_match_set p T (t_remove T (m5_kp M)) M K _ _ HmK eq_refl); [|reflexivity].
        cbn [t_remove t_L m5_unhash m5_set_refs m5_hashed]. apply hkp5_lem_put_vin_vremove_same.
      * reflexivity.
      * intros a Ha. apply hkp5_lem_put_vin_vremove; auto.
      * apply hkp5_lem_put_ind_remove; auto.
      * apply hkp5_lem_put_wf_remove; auto.
      * intros x Hx. apply hkp5_lem_put_cnt_rm_other; auto.
      * intros x Hx. eapply hkp5_lem_put_in_rm; eauto.
      * intros x Hx Hx'. apply hkp5_lem_put_in_rm_other; auto.
      * right. hlp_proj. rewrite Hr, hkp5_lem_put_cnt_rm_same by auto. rep_lia.
      * hlp_proj. discriminate.
Qed.

Lemma hkp5_lem_put_fact_put_held : hk5_fact_put_held.
Proof.
  intros p OD OH R ML KS T S fr mw w0 w m M unref Hc Hw HM Hh.
  pose proof Hc as (HF2 & HnML & HzML & HnKS & HzKS & HR & Hcnt & Hhash & Hpool).
  assert (HmML: In m (map fst ML)) by exact (in_map fst _ _ (hkp5_lem_put_afind_In _ _ _ HM)).
  assert (Hm: m <> nullval). { intros E. apply HzML. rewrite <- E. exact HmML. }
  destruct (hkp5_lem_put_F2_in p T ML KS m M HF2 (hkp5_lem_put_afind_In _ _ _ HM)) as (K & IK & HmK).
  assert (HK: afind KS (m5_kp M) = Some K) by exact (hkp5_lem_put_afind_nodup KS (m5_kp M, K) HnKS IK).
  assert (Hknz: m5_kp M <> nullval). { intros E. apply HzKS. rewrite <- E. exact (in_map fst _ _ IK). }
  pose proof HmK as (HKr & HKD & HKv & _).
  assert (HhM: m5_hashed M = true -> In m R).
  { rewrite Forall_forall in Hhash. exact (Hhash (m, M) (hkp5_lem_put_afind_In _ _ _ HM)). }
  pose proof (Int64.unsigned_range (m5_held M)) as Hh'.
  assert (HM2: afind (aupd ML m (m5_set_held M (Int64.sub (m5_held M) Int64.one))) m =
               Some (m5_set_held M (Int64.sub (m5_held M) Int64.one)))
    by exact (hkp5_lem_put_afind_aupd ML m _ M HM).
  cbv zeta.
  unfold hk5_put, kp_put, kp_put_warn. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec m nullval); [contradiction|].
  destruct (eq_dec (m5_kp M) nullval); [contradiction|].
  rewrite HM2, HK, HKr.
  change (m5_refs (m5_set_held M (Int64.sub (m5_held M) Int64.one))) with (m5_refs M).
  destruct Hpool as (_ & _ & _ & _ & _ & _ & HnI & Hwf).
  destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED) eqn:Hsat.
  - (* saturated: the count stays, a warning on both sides *)
    apply Int.same_if_eq in Hsat. rewrite Hsat, hkp5_lem_put_sub1_sat, hkp5_lem_put_dec_sat.
    change (Int.eq REFCOUNT_SATURATED Int.zero) with false.
    destruct unref; cbv beta iota zeta; cbn [kw_KS kw_T kw_S]; rewrite ?hkp5_lem_put_aupd_aupd;
      (refine (conj _ (conj (hkp5_lem_put_warn_bump _ _ _ Hw)
                       (or_introl (conj eq_refl (conj eq_refl (hkp5_lem_put_Zlength_aupd _ _ _))))))).
    + apply (hkp5_lem_put_upd p OD OH R R ML KS T (t_remove T (m5_kp M)) m M
               (m5_unhash (m5_set_held M (Int64.sub (m5_held M) Int64.one)))
               (kp_set_refs K REFCOUNT_SATURATED) Hc HM eq_refl).
      * apply (hkp5_lem_put_match_set p T (t_remove T (m5_kp M)) M K _ REFCOUNT_SATURATED HmK eq_refl).
        -- cbn [t_remove t_L m5_unhash m5_hashed]. apply hkp5_lem_put_vin_vremove_same.
        -- rewrite <- Hsat. reflexivity.
      * reflexivity.
      * intros a Ha. apply hkp5_lem_put_vin_vremove; auto.
      * apply hkp5_lem_put_ind_remove; auto.
      * apply hkp5_lem_put_wf_remove; auto.
      * intros x Hx. reflexivity.
      * auto.
      * auto.
      * left. exact Hsat.
      * hlp_proj. discriminate.
    + apply (hkp5_lem_put_upd p OD OH R R ML KS T T m M
               (m5_set_held M (Int64.sub (m5_held M) Int64.one))
               (kp_set_refs K REFCOUNT_SATURATED) Hc HM eq_refl).
      * apply (hkp5_lem_put_match_set p T T M K _ REFCOUNT_SATURATED HmK eq_refl).
        -- hlp_proj. exact HKv.
        -- rewrite <- Hsat. reflexivity.
      * reflexivity.
      * intros a Ha. reflexivity.
      * exact HnI.
      * exact Hwf.
      * intros x Hx. reflexivity.
      * auto.
      * auto.
      * left. exact Hsat.
      * hlp_proj. exact HhM.
  - (* below saturation: -1, no warning *)
    assert (HcM: Int.unsigned (m5_refs M) = hk5_cnt R m + Int64.unsigned (m5_held M) /\
                 1 <= Int.unsigned (m5_refs M) <= Int.max_signed).
    { rewrite Forall_forall in Hcnt. destruct (Hcnt (m, M) (hkp5_lem_put_afind_In _ _ _ HM)) as [E|E];
        [|exact E].
      cbn [snd] in E. rewrite E, Int.eq_true in Hsat. discriminate. }
    pose proof (hkp5_lem_put_cnt_nonneg m R) as Hc0.
    rewrite rc_sub1_small by rep_lia. rewrite rc_dec_warn_small by rep_lia.
    pose proof (hkp5_lem_put_sub_one (m5_refs M) (proj1 (proj2 HcM))) as Hr.
    pose proof (hkp5_lem_put_sub_one64 (m5_held M) ltac:(lia)) as Hh1.
    destruct (Int.eq (Int.sub (m5_refs M) Int.one) Int.zero) eqn:Hz.
    + (* the last reference: freed on both sides *)
      apply Int.same_if_eq in Hz. rewrite Hz, Int.unsigned_zero in Hr.
      assert (Hc2: hk5_cnt R m = 0) by lia.
      assert (HmR: ~ In m R) by (apply hkp5_lem_put_cnt_zero; auto).
      destruct unref; cbv beta iota zeta; cbn [kw_KS kw_T kw_S];
        rewrite ?hkp5_lem_put_t_free_remove, hkp5_lem_put_adel_aupd;
        (refine (conj _ (conj Hw (or_intror (conj eq_refl (conj eq_refl
                  (conj (hkp5_lem_put_Zlength_adel _ _ HmML) (conj _ HmR)))))))).
      * apply (hkp5_lem_put_del p OD OH R R ML KS T m M Hc HM); auto.
      * rewrite hkp5_lem_put_in_fst_adel by auto. tauto.
      * apply (hkp5_lem_put_del p OD OH R R ML KS T m M Hc HM); auto.
      * rewrite hkp5_lem_put_in_fst_adel by auto. tauto.
    + (* still referenced *)
      assert (Hz': Int.sub (m5_refs M) Int.one <> Int.zero).
      { intros E. rewrite E, Int.eq_true in Hz. discriminate. }
      assert (Hr1: 1 <= Int.unsigned (Int.sub (m5_refs M) Int.one)).
      { destruct (zeq (Int.unsigned (Int.sub (m5_refs M) Int.one)) 0) as [E|E]; [|rep_lia].
        exfalso. apply Hz'. rewrite <- (Int.repr_unsigned (Int.sub _ _)), E. reflexivity. }
      destruct unref; cbv beta iota zeta; cbn [kw_KS kw_T kw_S]; rewrite ?hkp5_lem_put_aupd_aupd;
        (refine (conj _ (conj Hw (or_introl (conj eq_refl (conj eq_refl
                  (hkp5_lem_put_Zlength_aupd _ _ _))))))).
      * apply (hkp5_lem_put_upd p OD OH R R ML KS T (t_remove T (m5_kp M)) m M
                 (m5_set_refs (m5_unhash (m5_set_held M (Int64.sub (m5_held M) Int64.one)))
                              (Int.sub (m5_refs M) Int.one))
                 (kp_set_refs K (Int.sub (m5_refs M) Int.one)) Hc HM eq_refl).
        -- apply (hkp5_lem_put_match_set p T (t_remove T (m5_kp M)) M K _ _ HmK eq_refl); [|reflexivity].
           cbn [t_remove t_L m5_unhash m5_set_refs m5_set_held m5_hashed].
           apply hkp5_lem_put_vin_vremove_same.
        -- reflexivity.
        -- intros a Ha. apply hkp5_lem_put_vin_vremove; auto.
        -- apply hkp5_lem_put_ind_remove; auto.
        -- apply hkp5_lem_put_wf_remove; auto.
        -- intros x Hx. reflexivity.
        -- auto.
        -- auto.
        -- right. hlp_proj. rewrite Hr, Hh1. rep_lia.
        -- hlp_proj. discriminate.
      * apply (hkp5_lem_put_upd p OD OH R R ML KS T T m M
                 (m5_set_refs (m5_set_held M (Int64.sub (m5_held M) Int64.one)) (Int.sub (m5_refs M) Int.one))
                 (kp_set_refs K (Int.sub (m5_refs M) Int.one)) Hc HM eq_refl).
        -- apply (hkp5_lem_put_match_set p T T M K _ _ HmK eq_refl); [|reflexivity].
           hlp_proj. exact HKv.
        -- reflexivity.
        -- intros a Ha. reflexivity.
        -- exact HnI.
        -- exact Hwf.
        -- intros x Hx. reflexivity.
        -- auto.
        -- auto.
        -- right. hlp_proj. rewrite Hr, Hh1. rep_lia.
        -- hlp_proj. exact HhM.
Qed.

Lemma hkp5_lem_put : hk5_fact_put /\ hk5_fact_put_held.
Proof.
  exact (conj hkp5_lem_put_fact_put hkp5_lem_put_fact_put_held).
Qed.
