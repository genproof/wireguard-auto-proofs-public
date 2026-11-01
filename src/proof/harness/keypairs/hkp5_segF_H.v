(* law keypairs, segment F piece H: statement 32 of main (the loop putting
   every held reference: for (k = live; k; k = kn) { kn = k->next; while (k->held > 0) { ... } }),
   hkp5_segF_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
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
Require Import WgNoise.proof.harness.keypairs.hkp5_segF_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* The model side of one held put: copied from hkp5_segOp6.v (prefix hk5o6_ -> hkHF6_) *)
Lemma hkHF6_afind_in {A: Type} (l: list (val * A)) k K : afind l k = Some K -> In k (map fst l).
Proof.
  induction l as [|[x v] l IH]; simpl; [discriminate|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|N]; auto.
Qed.

Lemma hkHF6_in_afind {A: Type} (l: list (val * A)) k K : NoDup (map fst l) -> In (k, K) l -> afind l k = Some K.
Proof.
  induction l as [|[x v] l IH]; simpl; [contradiction|]. intros ND I. inv ND. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|N].
  - destruct I as [E|I]; [congruence|]. exfalso. apply H1. change x with (fst (x, K)). apply in_map, I.
  - destruct I as [E|I]; [congruence|]. auto.
Qed.

Lemma hkHF6_afind_adel {A: Type} (l: list (val * A)) s m : m <> s -> afind (adel l s) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hkHF6_afind_adel_same {A: Type} (l: list (val * A)) s : NoDup (map fst l) -> afind (adel l s) s = None.
Proof.
  induction l as [|[x w] l IH]; simpl; [reflexivity|]. intros ND. inv ND. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - clear IH. induction l as [|[y u] l IHl]; simpl; [reflexivity|].
    destruct (EqDec_val y x) as [<-|Ny]; [exfalso; apply H1; left; reflexivity|].
    inv H2. apply IHl; auto. intros I; apply H1; right; exact I.
  - destruct (EqDec_val x s); [congruence|]. auto.
Qed.

Lemma hkHF6_afind_aupd {A: Type} (l: list (val * A)) s v m : m <> s -> afind (aupd l s v) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hkHF6_afind_aupd_same {A: Type} (l: list (val * A)) a v M :
  afind l a = Some M -> afind (aupd l a v) a = Some v.
Proof.
  induction l as [| [x w] l IH]; simpl; [discriminate |]. unfold eq_dec in *.
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - rewrite if_true by auto. reflexivity.
  - rewrite if_false by auto. exact IH.
Qed.

Lemma hkHF6_map_fst_aupd {A: Type} (l: list (val * A)) a v : map fst (aupd l a v) = map fst l.
Proof.
  induction l as [| [x w] l IH]; simpl; [reflexivity |]. unfold eq_dec in *. destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma hkHF6_head_aupd {A: Type} (l: list (val * A)) a v : hk5_head (aupd l a v) = hk5_head l.
Proof. destruct l as [| [x w] l]; simpl; [reflexivity |]. unfold eq_dec. destruct (EqDec_val x a); reflexivity. Qed.

(* the keypair addresses of the nodes are kept *)
Definition hkHF6_kpp (ML ML': list (val * hk5_mk)) : Prop :=
  forall x M', afind ML' x = Some M' -> exists M'', afind ML x = Some M'' /\ m5_kp M'' = m5_kp M'.

Lemma hkHF6_kpp_trans a b c : hkHF6_kpp a b -> hkHF6_kpp b c -> hkHF6_kpp a c.
Proof.
  intros Hab Hbc x M' E. destruct (Hbc x M' E) as (M1 & E1 & K1). destruct (Hab x M1 E1) as (M2 & E2 & K2).
  exists M2. split; congruence.
Qed.

Lemma hkHF6_kpp_aupd ML m M M' : afind ML m = Some M -> m5_kp M' = m5_kp M -> hkHF6_kpp ML (aupd ML m M').
Proof.
  intros E K x M1 E1. destruct (eq_dec x m) as [->|N].
  - rewrite (hkHF6_afind_aupd_same _ _ _ _ E) in E1. inv E1. eauto.
  - rewrite hkHF6_afind_aupd in E1 by auto. eauto.
Qed.

Lemma hkHF6_kpp_put m u ML fr mw : NoDup (map fst ML) -> hkHF6_kpp ML (fst (fst (hk5_put m u ML fr mw))).
Proof.
  intros ND. unfold hk5_put. destruct (eq_dec m nullval).
  { intros x M' E; eauto. }
  destruct (afind ML m) as [M|] eqn:EM; [| intros x M' E; eauto]. cbv zeta.
  destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED).
  - destruct u; cbn [fst]; [apply (hkHF6_kpp_aupd _ _ _ _ EM); reflexivity |]. intros x M' E; eauto.
  - destruct (Int.eq _ _); cbn [fst].
    + intros x M' E. destruct (eq_dec x m) as [->|N].
      * rewrite hkHF6_afind_adel_same in E by auto. discriminate.
      * rewrite hkHF6_afind_adel in E by auto. eauto.
    + apply (hkHF6_kpp_aupd _ _ _ _ EM). destruct u; reflexivity.
Qed.

Lemma hkHF6_slot_kpp ML ML' x : hkHF6_kpp ML ML' -> NoDup (map fst ML') ->
  (x = nullval \/ In x (map fst ML')) -> hk5_slot_kp ML' x = hk5_slot_kp ML x.
Proof.
  intros K ND Hx. unfold hk5_slot_kp. destruct (eq_dec x nullval); [reflexivity|].
  destruct Hx as [|Hx]; [contradiction|].
  apply list_in_map_inv in Hx. destruct Hx as ([y M'] & Ey & I). cbn [fst] in Ey. subst y.
  rewrite (hkHF6_in_afind _ _ _ ND I). destruct (K x M' (hkHF6_in_afind _ _ _ ND I)) as (M'' & E & KE).
  rewrite E. auto.
Qed.

Lemma hkHF6_vin_vremove a k L : a <> k -> vin a (vremove k L) = vin a L.
Proof.
  intros N. unfold vin.
  assert (E: In a (vremove k L) <-> In a L).
  { induction L as [|x L IH]; simpl; [tauto|]. unfold eq_dec in *.
    destruct (EqDec_val x k) as [<-|Nx]; simpl; rewrite IH; split; intros H; auto;
      destruct H as [<-|H]; auto; congruence. }
  destruct (in_dec eq_dec a (vremove k L)), (in_dec eq_dec a L); tauto.
Qed.

Lemma hkHF6_sfind_sdel {A: Type} (D: list (val * share * A)) a k : a <> k -> sfind (sdel D k) a = sfind D a.
Proof.
  intros N. induction D as [|[[x sh] e] D IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|Nx]; simpl.
  - destruct (EqDec_val x a); [congruence | reflexivity].
  - destruct (EqDec_val x a); [reflexivity | exact IH].
Qed.

(* a put of one of P's keypairs keeps the handshake entry and its membership *)
Lemma hkHF6_put_hs a k u KS T S : ~ In a (map fst KS) ->
  t_entry (kw_T (kp_put k u (mkKW KS T S))) a = t_entry T a /\
  vin a (t_L (kw_T (kp_put k u (mkKW KS T S)))) = vin a (t_L T).
Proof.
  intros NI. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec k nullval); [auto|]. destruct (afind KS k) as [K|] eqn:EK; [|auto].
  assert (Nk: a <> k) by (intros ->; apply NI; eapply hkHF6_afind_in; eauto).
  assert (E1: t_entry (if u then t_remove T k else T) a = t_entry T a /\
              vin a (t_L (if u then t_remove T k else T)) = vin a (t_L T)).
  { destruct u; [|auto]. unfold t_remove, t_entry. cbn [t_D t_L]. split; [reflexivity|].
    apply hkHF6_vin_vremove; auto. }
  destruct (Int.eq _ _); cbn [kw_T]; [|exact E1].
  destruct E1 as [E1 E2]. unfold t_free, t_entry in *. cbn [t_D t_L] in *.
  rewrite hkHF6_sfind_sdel by auto. rewrite hkHF6_vin_vremove by auto. auto.
Qed.

Lemma hkHF6_acc S fr n S' fr' n' f0 a0 :
  Int64.sub (s_frees S) f0 = fr -> Int64.sub (s_allocs S) a0 = Int64.add fr (Int64.repr n) ->
  ((S' = S /\ fr' = fr /\ n' = n) \/ (S' = shim_free S /\ fr' = Int64.add fr Int64.one /\ n' = n - 1)) ->
  Int64.sub (s_frees S') f0 = fr' /\ Int64.sub (s_allocs S') a0 = Int64.add fr' (Int64.repr n').
Proof.
  intros E1 E2 [(->&->&->)|(->&->&->)]; [auto|]. cbn [s_frees s_allocs shim_free]. split.
  - rewrite Int64.sub_add_l, E1. reflexivity.
  - rewrite E2, Int64.add_assoc. f_equal. unfold Int64.one. rewrite add64_repr. f_equal. lia.
Qed.

Lemma hkHF6_held_pos (h: int64) : h <> Int64.zero -> Int64.unsigned h > 0.
Proof.
  intros N. pose proof (Int64.unsigned_range h).
  destruct (Z.eq_dec (Int64.unsigned h) 0) as [E|]; [|lia].
  exfalso. apply N. rewrite <- (Int64.repr_unsigned h), E. reflexivity.
Qed.

Lemma hkHF6_and1 u : 0 <= u <= Byte.max_unsigned ->
  Int.and (Int.repr u) (Int.repr 1) = if Z.odd u then Int.one else Int.zero.
Proof.
  intros Hu. unfold Int.and. rewrite Int.unsigned_repr by rep_lia.
  change (Int.unsigned (Int.repr 1)) with (Z.ones 1). rewrite Z.land_ones by lia.
  rewrite Zmod_odd. destruct (Z.odd u); reflexivity.
Qed.

(* the whole model step of op 6 on a held node m *)
Lemma hkHF6_model (MF: hkp5_model_facts) p OD OH ML sp sc sn fr mw P KS T S w0 w m M u ML' fr' mw' :
  hk5_rel p OD OH (mkH5 ML sp sc sn fr mw) P KS T -> hk5_warn_ok w0 mw w ->
  afind ML m = Some M -> m5_held M <> Int64.zero ->
  hk5_put m u (aupd ML m (m5_set_held M (Int64.sub (m5_held M) Int64.one))) fr mw = (ML', fr', mw') ->
  kps_in_pool T p KS /\ In (m5_kp M) (map fst KS) /\
  hk5_rel p OD OH (mkH5 ML' sp sc sn fr' mw') P (kw_KS (kp_put (m5_kp M) u (mkKW KS T S)))
    (kw_T (kp_put (m5_kp M) u (mkKW KS T S))) /\
  hk5_warn_ok w0 mw' (kp_put_warn (m5_kp M) KS w) /\
  t_entry (kw_T (kp_put (m5_kp M) u (mkKW KS T S))) (hs_addr p) = t_entry T (hs_addr p) /\
  vin (hs_addr p) (t_L (kw_T (kp_put (m5_kp M) u (mkKW KS T S)))) = vin (hs_addr p) (t_L T) /\
  (forall f0 a0, Int64.sub (s_frees S) f0 = fr -> Int64.sub (s_allocs S) a0 = Int64.add fr (Int64.repr (Zlength ML)) ->
     Int64.sub (s_frees (kw_S (kp_put (m5_kp M) u (mkKW KS T S)))) f0 = fr' /\
     Int64.sub (s_allocs (kw_S (kp_put (m5_kp M) u (mkKW KS T S)))) a0 = Int64.add fr' (Int64.repr (Zlength ML'))).
Proof.
  intros R Wk EM HM E.
  destruct MF as (FPre & FS & FPm & FP & FH & _).
  destruct R as (C0 & ND & Ep & Ec & En).
  cbn [hk5_slots h5_sp h5_sc h5_sn h5_ML] in C0, ND, Ep, Ec, En.
  pose proof (FPre _ _ _ _ _ _ _ C0) as (KP & _ & Hnk & _).
  destruct (Hnk m M EM) as (K & EK & _).
  pose proof (FH p OD OH _ ML KS T S fr mw w0 w m M u C0 Wk EM (hkHF6_held_pos _ HM)) as FHm.
  cbv zeta in FHm. rewrite E in FHm. destruct FHm as (C' & Wk' & D).
  pose proof C0 as (_ & ND0 & _ & _ & _ & _ & _ & _ & (_ & NIhs & _)).
  set (ML1 := aupd ML m (m5_set_held M (Int64.sub (m5_held M) Int64.one))) in E.
  assert (ND1: NoDup (map fst ML1)) by (unfold ML1; rewrite hkHF6_map_fst_aupd; exact ND0).
  assert (K1: hkHF6_kpp ML ML') .
  { apply hkHF6_kpp_trans with ML1; [apply (hkHF6_kpp_aupd _ _ _ _ EM); reflexivity |].
    pose proof (hkHF6_kpp_put m u ML1 fr mw ND1) as KK. rewrite E in KK. exact KK. }
  pose proof C' as (_ & ND' & _ & _ & _ & CF' & _). rewrite Forall_forall in CF'.
  split; [exact KP|]. split; [eapply hkHF6_afind_in; eauto|].
  split.
  { unfold hk5_rel. cbn [hk5_slots h5_sp h5_sc h5_sn h5_ML].
    split; [exact C'|]. split; [exact ND|].
    rewrite !(hkHF6_slot_kpp ML ML') by (auto; apply CF'; simpl; tauto). auto. }
  split; [exact Wk'|].
  destruct (hkHF6_put_hs (hs_addr p) (m5_kp M) u KS T S NIhs) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  intros f0 a0 F1 F2. apply (hkHF6_acc _ _ _ _ _ _ f0 a0 F1 F2).
  destruct D as [(D1&D2&D3)|(D1&D2&D3&_)]; [left|right]; auto.
Qed.

(* one held put (unref = false) on the loop invariant *)
Lemma hkHF_inv_step (MF: hkp5_model_facts) F V S wn kc P KS T ML fr mw now next_id id_known hsn k M ML' fr' mw' :
  hkp5_inv F V (mkKY5 S wn kc P KS T (mkH5 ML nullval nullval nullval fr mw) now next_id id_known hsn) ->
  afind ML k = Some M -> m5_held M <> Int64.zero ->
  hk5_put k false (aupd ML k (m5_set_held M (Int64.sub (m5_held M) Int64.one))) fr mw = (ML', fr', mw') ->
  hkp5_inv F V (mkKY5 (kw_S (kp_put (m5_kp M) false (mkKW KS T S))) (kp_put_warn (m5_kp M) KS wn) kc P
     (kw_KS (kp_put (m5_kp M) false (mkKW KS T S))) (kw_T (kp_put (m5_kp M) false (mkKW KS T S)))
     (mkH5 ML' nullval nullval nullval fr' mw') now next_id id_known hsn).
Proof.
  intros Hinv EM HM EP.
  destruct Hinv as (Hrel & Hwarn & Hdev & Hsid & Hpr & Hfr & Hal & Hid & Hnow & Hhsm).
  cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn h5_ML h5_frees h5_warn] in *.
  destruct (hkHF6_model MF (f_p F) (v_OD V) (v_OH V) ML nullval nullval nullval fr mw P KS T S (v_w0 V) wn k M false
              ML' fr' mw' Hrel Hwarn EM HM EP) as (_ & _ & Rel' & Warn' & Hent & Hvin & Acc).
  destruct (Acc _ _ Hfr Hal) as [A1 A2].
  destruct Hhsm as ((Hh1 & Hh2 & Hh3) & Hpk).
  unfold hkp5_inv, hk5_hsm_ok. cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn h5_ML
    h5_frees h5_warn].
  rewrite <- Hent in Hh1. rewrite <- Hvin in Hh2.
  exact (conj Rel' (conj Warn' (conj Hdev (conj Hsid (conj Hpr (conj A1 (conj A2 (conj Hid (conj Hnow
    (conj (conj Hh1 (conj Hh2 Hh3)) Hpk)))))))))).
Qed.

(* ---------------------------------------------------------------------- *)
(* Pure helpers                                                            *)
(* ---------------------------------------------------------------------- *)

Lemma hkHF_nodup_mid {A: Type} (pre rest: list (val * A)) k M :
  NoDup (map fst (pre ++ (k, M) :: rest)) -> ~ In k (map fst pre).
Proof.
  rewrite map_app. cbn [map fst]. intros ND I.
  apply NoDup_remove_2 in ND. apply ND. apply in_or_app. left. exact I.
Qed.

Lemma hkHF_afind_mid {A: Type} (pre rest: list (val * A)) k M :
  ~ In k (map fst pre) -> afind (pre ++ (k, M) :: rest) k = Some M.
Proof.
  induction pre as [|[x X] pre IH]; cbn [app afind map fst In]; intros NI.
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by (intros ->; apply NI; left; reflexivity). apply IH. tauto.
Qed.

Lemma hkHF_aupd_mid {A: Type} (pre rest: list (val * A)) k M v :
  ~ In k (map fst pre) -> aupd (pre ++ (k, M) :: rest) k v = pre ++ (k, v) :: rest.
Proof.
  induction pre as [|[x X] pre IH]; cbn [app aupd map fst In]; intros NI.
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by (intros ->; apply NI; left; reflexivity). rewrite IH by tauto. reflexivity.
Qed.

Lemma hkHF_adel_mid {A: Type} (pre rest: list (val * A)) k M :
  ~ In k (map fst pre) -> adel (pre ++ (k, M) :: rest) k = pre ++ rest.
Proof.
  induction pre as [|[x X] pre IH]; cbn [app adel map fst In]; intros NI.
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by (intros ->; apply NI; left; reflexivity). rewrite IH by tauto. reflexivity.
Qed.

Lemma hkHF_put_mid pre k M rest fr mw : k <> nullval -> ~ In k (map fst pre) ->
  hk5_put k false (pre ++ (k, M) :: rest) fr mw =
  if Int.eq (m5_refs M) REFCOUNT_SATURATED then (pre ++ (k, M) :: rest, fr, warn_bump mw REFCOUNT_SUB_UAF)
  else if Int.eq (Int.sub (m5_refs M) Int.one) Int.zero then (pre ++ rest, Int64.add fr Int64.one, mw)
  else (pre ++ (k, m5_set_refs M (Int.sub (m5_refs M) Int.one)) :: rest, fr, mw).
Proof.
  intros Nk NI. unfold hk5_put. rewrite if_false by exact Nk. rewrite hkHF_afind_mid by exact NI. cbv zeta.
  destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED); [reflexivity|].
  destruct (Int.eq _ Int.zero); [rewrite hkHF_adel_mid by exact NI; reflexivity|].
  rewrite hkHF_aupd_mid by exact NI. reflexivity.
Qed.

Lemma hkHF_sub_one_zero (r: int) : Int.sub r Int.one = Int.zero -> r = Int.one.
Proof.
  intros E. assert (X: r = Int.add (Int.sub r Int.one) Int.one).
  { rewrite Int.sub_add_opp, Int.add_assoc, (Int.add_commut (Int.neg Int.one)), Int.add_neg_zero, Int.add_zero.
    reflexivity. }
  rewrite E, Int.add_zero_l in X. exact X.
Qed.

Lemma hkHF_put_free pre k M rest fr mw : k <> nullval -> ~ In k (map fst pre) -> m5_refs M = Int.one ->
  hk5_put k false (pre ++ (k, M) :: rest) fr mw = (pre ++ rest, Int64.add fr Int64.one, mw).
Proof.
  intros Nk NI E. rewrite hkHF_put_mid by auto. rewrite E. reflexivity.
Qed.

Lemma hkHF_put_keep pre k M rest fr mw ML' fr' mw' : k <> nullval -> ~ In k (map fst pre) ->
  m5_refs M <> Int.one -> hk5_put k false (pre ++ (k, M) :: rest) fr mw = (ML', fr', mw') ->
  exists M', ML' = pre ++ (k, M') :: rest /\ m5_send M' = m5_send M /\ m5_recv M' = m5_recv M.
Proof.
  intros Nk NI N1 EP. rewrite hkHF_put_mid in EP by auto.
  destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED).
  - inv EP. exists M. auto.
  - destruct (Int.eq (Int.sub (m5_refs M) Int.one) Int.zero) eqn:E0.
    + apply Int.same_if_eq in E0. apply hkHF_sub_one_zero in E0. contradiction.
    + inv EP. eexists. split; [reflexivity|]. split; reflexivity.
Qed.

(* with no slot, a node's count is saturated or its held references *)
Lemma hkHF_count p OD OH ML sp sc sn fr mw P KS T m M :
  hk5_rel p OD OH (mkH5 ML sp sc sn fr mw) P KS T -> sp = nullval -> sc = nullval -> sn = nullval ->
  afind ML m = Some M ->
  m5_refs M = REFCOUNT_SATURATED \/
  (Int.unsigned (m5_refs M) = Int64.unsigned (m5_held M) /\ 1 <= Int.unsigned (m5_refs M) <= Int.max_signed).
Proof.
  intros (C & _) -> -> -> E. unfold hk5_slots in C. cbn [h5_sp h5_sc h5_sn h5_ML] in C.
  destruct C as (_ & ND & NN & _ & _ & _ & CF & _).
  assert (I: In (m, M) ML).
  { clear - E. induction ML as [|[x X] ML IH]; cbn [afind] in E; [discriminate|].
    destruct (eq_dec x m) as [<-|N]; [inv E; left; reflexivity | right; auto]. }
  rewrite Forall_forall in CF. specialize (CF _ I). cbn [fst snd] in CF.
  assert (Nm: m <> nullval) by (intros ->; apply NN; change nullval with (fst (nullval, M)); apply in_map, I).
  assert (Z0: hk5_cnt [nullval; nullval; nullval] m = 0).
  { unfold hk5_cnt, hk5_eqb. cbn [filter]. rewrite !if_false by auto. reflexivity. }
  destruct CF as [S|(E1 & E2)]; [left; exact S | right]. 
  unfold hk5_slots in E1; cbn [h5_sp h5_sc h5_sn] in E1. rewrite Z0 in E1. split; lia.
Qed.

Lemma hkHF_head_mid {A: Type} (pre rest: list (val * A)) k M M' :
  hk5_head (pre ++ (k, M) :: rest) = hk5_head (pre ++ (k, M') :: rest).
Proof. destruct pre as [|[x X] pre]; reflexivity. Qed.

Lemma hkHF_head_null (ML: list (val * hk5_mk)) : ~ In nullval (map fst ML) -> hk5_head ML = nullval -> ML = [].
Proof. destruct ML as [|[x X] ML]; cbn; [auto|]. intros N E. subst x. exfalso. apply N. left. reflexivity. Qed.

Section VSTside.
#[local] Existing Instance W_keypairs.

Lemma hkHF6_kp_ptr KS k : In k (map fst KS) -> keypairs_rep W_keypairs KS |-- !! isptr k.
Proof.
  induction KS as [| [x K] KS IH]; cbn [map fst In]; [tauto |].
  unfold keypairs_rep. cbn [iter_sepcon.iter_sepcon]. intros [-> | Hin].
  - unfold keypair_item_rep, keypair_rep at 1. rewrite sepcon_andp_prop'. apply andp_left1.
    apply prop_derives. intros [Hfc _]. exact (field_compatible_isptr _ _ _ Hfc).
  - sep_apply (IH Hin). Intros. apply prop_right; auto.
Qed.

Lemma hkHF_len (pre rest: list (val * hk5_mk)) k (M: hk5_mk) : hk5_mklist (pre ++ (k, M) :: rest) |--
  !! (Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32).
Proof.
  induction pre as [|[x X] pre IH]; cbn [app hk5_mklist].
  - unfold hk5_node. entailer!.
  - sep_apply IH. entailer!.
Qed.

Lemma hkHF_focus (pre rest: list (val * hk5_mk)) k (M: hk5_mk) : exists Rst, forall M',
  Zlength (m5_send M') = 32 -> Zlength (m5_recv M') = 32 ->
  hk5_mklist (pre ++ (k, M') :: rest) = (data_at Ews t_mk5 (hk5_mk_val M' (hk5_head rest)) k * Rst)%logic.
Proof.
  induction pre as [|[x X] pre IH].
  - exists (malloc_token Ews t_mk5 k * hk5_mklist rest)%logic. intros M' L1 L2. cbn [app hk5_mklist].
    unfold hk5_node. rewrite prop_true_andp by auto. rewrite sepcon_assoc. reflexivity.
  - destruct IH as (Rst & IH). exists (hk5_node x X (hk5_head (pre ++ (k, M) :: rest)) * Rst)%logic.
    intros M' L1 L2. cbn [app hk5_mklist]. rewrite (hkHF_head_mid pre rest k M' M), IH by auto.
    rewrite <- !sepcon_assoc, (sepcon_comm (hk5_node _ _ _)). reflexivity.
Qed.

Lemma hkHF_head_ptr_app (pre ML: list (val * hk5_mk)) :
  hk5_mklist (pre ++ ML) |-- !! is_pointer_or_null (hk5_head ML).
Proof.
  induction pre as [|[x X] pre IH]; cbn [app hk5_mklist].
  - destruct ML as [|[x X] ML]; cbn [hk5_mklist hk5_head]; [entailer!|]. unfold hk5_node. entailer!.
  - sep_apply IH. entailer!.
Qed.

Lemma hkHF_next_ptr (pre rest: list (val * hk5_mk)) k M :
  hk5_mklist (pre ++ (k, M) :: rest) |-- !! is_pointer_or_null (hk5_head rest).
Proof.
  replace (pre ++ (k, M) :: rest) with ((pre ++ [(k, M)]) ++ rest) by (rewrite <- app_assoc; reflexivity).
  apply hkHF_head_ptr_app.
Qed.

Lemma hkHF_head_ptr (ML: list (val * hk5_mk)) : hk5_mklist ML |-- !! is_pointer_or_null (hk5_head ML).
Proof. destruct ML as [|[x X] ML]; cbn [hk5_mklist hk5_head]; [entailer!|]. unfold hk5_node. entailer!. Qed.

End VSTside.

(* the loop states: outer (k or kn = the head of the rest, every node before it saturated) and inner *)
Section States.
Variable x25519: list byte -> list byte -> list byte.

Definition hkHF_sat (l: list (val * hk5_mk)) : Prop :=
  Forall (fun x => m5_refs (snd x) = REFCOUNT_SATURATED) l.

Definition hkHF_O (F: hkp5_fix) (V: hkp5_val) (steps: Z) (O: hkp5_oth) (FR: mpred) (kn: ident)
  : environ -> mpred :=
  EX Y: hkp5_dyn, EX pre: list (val * hk5_mk), EX rest: list (val * hk5_mk),
  PROPx [hkp5_fix_ok F V; hkp5_inv F V Y; hkp5F_P1 (y_H Y); h5_ML (y_H Y) = pre ++ rest; hkHF_sat pre]
  (LOCALx (temp kn (hk5_head rest) :: hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP x25519 F V Y (hkp5_othR x25519 F V O * FR)))).

Definition hkHF_I (F: hkp5_fix) (V: hkp5_val) (steps: Z) (O: hkp5_oth) (FR: mpred) (k: val)
  (pre rest: list (val * hk5_mk)) : environ -> mpred :=
  EX Y: hkp5_dyn, EX M: hk5_mk,
  PROPx [hkp5_fix_ok F V; hkp5_inv F V Y; hkp5F_P1 (y_H Y); h5_ML (y_H Y) = pre ++ (k, M) :: rest; hkHF_sat pre]
  (LOCALx (temp KC._k k :: temp KC._kn (hk5_head rest) :: hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP x25519 F V Y (hkp5_othR x25519 F V O * FR)))).

End States.

Ltac hkHF_norm := unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars;
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].

Lemma hkp5_segF_H_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps (O: hkp5_oth) (FR: mpred) R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_F x25519)) (hkp5F_S x25519 F V steps O FR hkp5F_P1) hkp5F_sH
    (overridePost (hkp5F_S x25519 F V steps O FR hkp5F_P2) R).
Proof.
  intros MF HX.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost, hkp5F_sH, hkp5_Delta.
  abbreviate_semax.
  destruct F as [gv w t pt p raw pub snap opub first second].
  set (F0 := {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
                f_snap := snap; f_opub := opub; f_first := first; f_second := second |}).
  set (FRo := (hkp5_othR x25519 F0 V O * FR)%logic).
  unfold hkp5F_S. fold FRo. Intros Y.
  destruct Y as [S wn kc P KS T HH now next_id id_known hsn].
  destruct HH as [ML sp sc sn fr mw].
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn] in H0, H1 |- *.
  assert_PROP (is_pointer_or_null (hk5_head ML)) as Hhd by (sep_apply (hkHF_head_ptr ML); entailer!).
  forward.
  forward_loop (hkHF_O x25519 F0 V steps O FR KC._k) continue: (hkHF_O x25519 F0 V steps O FR KC._kn)
    break: (hkp5F_S x25519 F0 V steps O FR hkp5F_P2).
  - unfold hkHF_O. Exists (mkKY5 S wn kc P KS T (mkH5 ML sp sc sn fr mw) now next_id id_known hsn)
      (@nil (val * hk5_mk)) ML.
    unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars. fold FRo.
    cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    entailer!. constructor.
  - clear H H0 H1 Hhd. clear S wn kc P KS T ML sp sc sn fr mw now next_id id_known hsn.
    unfold hkHF_O. Intros Y pre rest.
    destruct Y as [S wn kc P KS T HH now next_id id_known hsn].
    destruct HH as [ML sp sc sn fr mw].
    hkHF_norm. fold FRo.
    pose proof H0 as Hinv. destruct H0 as (Hrel & Hwarn & Hdev & Hsid & Hpr & Hfr & Hal & Hid & Hnow & Hhsm).
    cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn]
      in Hrel, Hwarn, Hdev, Hsid, Hpr, Hfr, Hal, Hid, Hnow, Hhsm, H1, H2.
    subst ML.
    destruct H1 as (Hsp & Hsc & Hsn). cbn [h5_sp h5_sc h5_sn] in Hsp, Hsc, Hsn. subst sp sc sn.
    destruct rest as [| [k M] rest].
    + (* the end of the list *)
      forward_if.
      * contradiction.
      * forward. unfold hkp5F_S.
        Exists (mkKY5 S wn kc P KS T (mkH5 (pre ++ []) nullval nullval nullval fr mw) now next_id id_known hsn).
        hkHF_norm. fold FRo. entailer!.
        split; [repeat split; reflexivity|]. rewrite app_nil_r. exact H3.
    + (* the node k *)
      pose proof Hrel as ((_ & ND & NN & _) & _). cbn [h5_ML] in ND, NN.
      assert (NI: ~ In k (map fst pre)) by exact (hkHF_nodup_mid _ _ _ _ ND).
      assert (Nk: k <> nullval).
      { intros ->. apply NN. rewrite map_app. apply in_or_app. right. left. reflexivity. }
      change (hk5_head ((k, M) :: rest)) with k.
      assert_PROP (Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32) as LL
        by (sep_apply (hkHF_len pre rest k M); entailer!).
      destruct LL as [L1 L2].
      assert_PROP (is_pointer_or_null (hk5_head rest)) as Hnx
        by (sep_apply (hkHF_next_ptr pre rest k M); entailer!).
      destruct (hkHF_focus pre rest k M) as (Rst & Foc). rewrite (Foc M L1 L2). Intros.
      assert_PROP (isptr k) as Hkp by entailer!.
      forward_if.
      2: { subst k. contradiction. }
      forward.
      forward_loop (hkHF_I x25519 F0 V steps O FR k pre rest) break: (hkHF_O x25519 F0 V steps O FR KC._kn).
      * unfold hkHF_I.
        Exists (mkKY5 S wn kc P KS T (mkH5 (pre ++ (k, M) :: rest) nullval nullval nullval fr mw) now next_id id_known hsn) M.
        hkHF_norm. fold FRo. rewrite (Foc M L1 L2). entailer!.
        unfold hkp5F_P1; cbn; auto.
      * clear H Hrel Hwarn Hdev Hsid Hpr Hfr Hal Hid Hnow Hhsm Hinv ND NN L1 L2 Rst Foc H0.
        clear S wn kc P KS T fr mw now next_id id_known hsn M.
        unfold hkHF_I. Intros Y M.
        destruct Y as [S wn kc P KS T HH now next_id id_known hsn].
        destruct HH as [ML sp sc sn fr mw].
        hkHF_norm. fold FRo.
        pose proof H0 as Hinv. destruct H0 as (Hrel & Hwarn & Hdev & Hsid & Hpr & Hfr & Hal & Hid & Hnow & Hhsm).
        cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
           y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn]
          in Hrel, Hwarn, Hdev, Hsid, Hpr, Hfr, Hal, Hid, Hnow, Hhsm, H1, H2.
        subst ML.
        destruct H1 as (Hsp & Hsc & Hsn). cbn [h5_sp h5_sc h5_sn] in Hsp, Hsc, Hsn. subst sp sc sn.
        assert_PROP (Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32) as LL
          by (sep_apply (hkHF_len pre rest k M); entailer!).
        destruct LL as [L1 L2].
        destruct (hkHF_focus pre rest k M) as (Rst & Foc). rewrite (Foc M L1 L2). Intros.
        assert (EM: afind (pre ++ (k, M) :: rest) k = Some M) by exact (hkHF_afind_mid _ _ _ _ NI).
        pose proof (hkHF_count _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel eq_refl eq_refl eq_refl EM) as Hcnt.
        forward.
        forward_if.
        2: { assert (Hsat: m5_refs M = REFCOUNT_SATURATED).
          { destruct Hcnt as [?|(E1&E2)]; [auto|]. rewrite Int64.unsigned_repr in H0 by rep_lia.
            pose proof (Int64.unsigned_range (m5_held M)). lia. }
          forward.
          unfold hkHF_O.
          Exists (mkKY5 S wn kc P KS T (mkH5 ((pre ++ [(k, M)]) ++ rest) nullval nullval nullval fr mw) now next_id id_known hsn)
            (pre ++ [(k, M)]) rest.
          hkHF_norm. fold FRo.
          replace ((pre ++ [(k, M)]) ++ rest) with (pre ++ (k, M) :: rest) by (rewrite <- app_assoc; reflexivity).
          rewrite (Foc M L1 L2). entailer!.
          split; [unfold hkp5F_P1; cbn; auto|].
          unfold hkHF_sat in *. apply Forall_app. split; [exact H3|]. constructor; [exact Hsat | constructor]. }
        assert (HM: m5_held M <> Int64.zero).
        { intros E. rewrite E in H0. rewrite Int64.unsigned_repr in H0 by rep_lia. cbn in H0. lia. }
        assert (HkKS: In (m5_kp M) (map fst KS)).
        { destruct (proj1 MF _ _ _ _ _ _ _ (proj1 Hrel)) as (_ & _ & Hnk & _). destruct (Hnk k M EM) as (K & EK & _).
          eapply hkHF6_afind_in; eauto. }
        assert_PROP (isptr (m5_kp M)) as Hkpp.
        { sep_apply (hkHF6_kp_ptr KS (m5_kp M) HkKS). entailer!. }
        set (M1 := m5_set_held M (Int64.sub (m5_held M) Int64.one)).
        pose proof (proj1 MF _ _ _ _ _ _ _ (proj1 Hrel)) as (KP & _).
        pose proof Hrel as ((_ & ND & _) & _). cbn [h5_ML] in ND.
        destruct (hk5_put k false (pre ++ (k, M1) :: rest) fr mw) as [[ML' fr'] mw'] eqn:EP.
        assert (EP': hk5_put k false (aupd (pre ++ (k, M) :: rest) k M1) fr mw = (ML', fr', mw'))
          by (rewrite hkHF_aupd_mid by exact NI; exact EP).
        pose proof (hkHF_inv_step MF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv EM HM EP') as Hinv'.
        clear Hinv Hrel Hwarn Hsid Hpr Hal Hid Hnow Hhsm EP'.
        forward. forward. forward.
        change (fst (hk5_mk_val M (hk5_head rest))) with (m5_kp M).
        replace_SEP 12 (data_at Ews t_mk5 (hk5_mk_val M1 (hk5_head rest)) k). { entailer!. }
        set (D := hkp5_D x25519 F0 V).
        change (itable Tsh (f_t F0) T) with (itable Tsh (d_itab D) T).
        forward_call (f_gv F0, S, wn, KS, T, m5_kp M, false, Tsh, f_p F0, P, Tsh, f_w F0, D, Tsh).
        change (d_itab D) with (f_t F0).
        forward.
        gather_SEP 14 15. rewrite <- (Foc M1 L1 L2).
        rewrite (hkHF_head_mid pre rest k M M1).
        assert (ND1: NoDup (map fst (pre ++ (k, M1) :: rest))) by (rewrite map_app; rewrite map_app in ND; exact ND).
        assert (IN1: In k (map fst (pre ++ (k, M1) :: rest))).
        { rewrite map_app. apply in_or_app. right. left. reflexivity. }
        forward_if.
        { forward_call (f_gv F0, pre ++ (k, M1) :: rest, fr, mw, k, false).
          pose proof (hkHF_put_free pre k M1 rest fr mw Nk NI H1) as EPf.
          rewrite EPf. rewrite EPf in EP. injection EP as E1 E2 E3. subst ML' fr' mw'.
          cbn [fst snd].
          forward.
          unfold hkHF_O.
          Exists (mkKY5 (kw_S (kp_put (m5_kp M) false {| kw_KS := KS; kw_T := T; kw_S := S |}))
                   (kp_put_warn (m5_kp M) KS wn) kc P
                   (kw_KS (kp_put (m5_kp M) false {| kw_KS := KS; kw_T := T; kw_S := S |}))
                   (kw_T (kp_put (m5_kp M) false {| kw_KS := KS; kw_T := T; kw_S := S |}))
                   (mkH5 (pre ++ rest) nullval nullval nullval (Int64.add fr Int64.one) mw) now next_id id_known hsn)
            pre rest.
          hkHF_norm. fold FRo. subst D.
          entailer!.
          unfold hkp5F_P1; cbn; auto. }
        forward_call (f_gv F0, pre ++ (k, M1) :: rest, fr, mw, k, false).
        destruct (hkHF_put_keep pre k M1 rest fr mw ML' fr' mw' Nk NI H1 EP) as (M' & EML & Es & Er).
        rewrite EP. cbn [fst snd]. subst ML'.
        unfold hkHF_I.
        Exists (mkKY5 (kw_S (kp_put (m5_kp M) false {| kw_KS := KS; kw_T := T; kw_S := S |}))
                 (kp_put_warn (m5_kp M) KS wn) kc P
                 (kw_KS (kp_put (m5_kp M) false {| kw_KS := KS; kw_T := T; kw_S := S |}))
                 (kw_T (kp_put (m5_kp M) false {| kw_KS := KS; kw_T := T; kw_S := S |}))
                 (mkH5 (pre ++ (k, M') :: rest) nullval nullval nullval fr' mw') now next_id id_known hsn) M'.
        hkHF_norm. fold FRo. subst D.
        entailer!.
        unfold hkp5F_P1; cbn; auto.
  - unfold hkHF_O. Intros Y pre rest. unfold hkp5_temps, hkp5_lvars. cbn [app]. forward.
    Exists Y pre rest. unfold hkp5_temps, hkp5_lvars. cbn [app]. entailer!.
  - unfold POSTCONDITION, abbreviate. cbn [RA_normal]. apply ENTAIL_refl.
Qed.
