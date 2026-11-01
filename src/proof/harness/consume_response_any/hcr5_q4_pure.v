(* law consume_response_any, phase Q4: pure helpers - the comparisons
   dev_same / kents_same / shim_same of unchanged objects are true (reflexivity of the eqb's), and their
   pointer preconditions (lent objects VO = [VItab ..; VPeers PS']) from the state's invariants. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require WgNoise.harness.x_consume_response_any.code.

Local Open Scope Z_scope.

(* ---- reflexivity of the comparisons ---- *)
Lemma hcr5_q4_veqb x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hcr5_q4_bytes A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

Lemma hcr5_q4_dev_refl D h : dev_eqb D h D h = true.
Proof.
  unfold dev_eqb. rewrite !hcr5_q4_veqb, !hcr5_q4_bytes, !Bool.eqb_reflx, !Int64.eq_true. reflexivity.
Qed.

Lemma hcr5_q4_shim_refl S w : shim_eqb S w S w = true.
Proof. unfold shim_eqb, warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity. Qed.

Lemma hcr5_q4_int64s l : int64s_eqb l l = true.
Proof. induction l as [| x l IH]; cbn; [reflexivity | rewrite Int64.eq_true, IH; reflexivity]. Qed.

Lemma hcr5_q4_symkey A : symkey_eqb A A = true.
Proof. unfold symkey_eqb. rewrite hcr5_q4_bytes, Int64.eq_true, Bool.eqb_reflx. reflexivity. Qed.

Lemma hcr5_q4_kp K : kp_eqb K K = true.
Proof.
  unfold kp_eqb. rewrite !hcr5_q4_symkey, !Int64.eq_true, !Int.eq_true, Bool.eqb_reflx, hcr5_q4_int64s.
  reflexivity.
Qed.

Lemma hcr5_q4_entry E : entry_eqb E E = true.
Proof. unfold entry_eqb. destruct (eq_dec (e_peer E) (e_peer E)); [| congruence]. rewrite !Int.eq_true. reflexivity. Qed.

Lemma hcr5_q4_kents_refl T KE : forallb (kent_same T) (map (kent_snapped T) KE) = true.
Proof.
  induction KE as [| e KE IH]; [reflexivity |]. cbn [map forallb]. rewrite IH, andb_true_r.
  unfold kent_same, kent_snapped, kent_eqb_cur, kent_eqb_nn; cbn.
  rewrite hcr5_q4_entry, Bool.eqb_reflx, hcr5_q4_kp, hcr5_q4_veqb. reflexivity.
Qed.

(* ---- the peers after the call: same addresses and shares ---- *)
Lemma hcr5_q4_supd_addrs (PS: list (val * share * peer)) a P' :
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [| [[x sh] Q] PS IH]; cbn; [reflexivity |].
  destruct (EqDec_val x a); cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hcr5_q4_after_addrs PS res : map peer_addr4 (peers_after PS res) = map peer_addr4 PS.
Proof. destruct res as [[a P'] |]; cbn; [apply hcr5_q4_supd_addrs | reflexivity]. Qed.

Lemma hcr5_q4_supd_sh (PS: list (val * share * peer)) a P' (Q: share -> Prop) :
  Forall (fun x : val * share * peer => match x with (_, sh, _) => Q sh end) PS ->
  Forall (fun x : val * share * peer => match x with (_, sh, _) => Q sh end) (supd PS a P').
Proof.
  induction PS as [| [[x sh] P] PS IH]; cbn; intros H; [constructor |].
  inversion H; subst. destruct (EqDec_val x a); constructor; auto.
Qed.

Lemma hcr5_q4_after_ok L KA PS res :
  Forall (hcr5_pok L KA) PS -> vobj_ok (VPeers (peers_after PS res)).
Proof.
  intros H. cbn.
  assert (H': Forall (fun x : val * share * peer => match x with (_, sh, _) => readable_share sh end) PS).
  { eapply Forall_impl; [| exact H]. intros [[a sh] P] (-> & _). apply writable_readable, writable_Ews. }
  destruct res as [[a P'] |]; cbn; [apply hcr5_q4_supd_sh |]; exact H'.
Qed.

(* ---- pure table facts ---- *)
Lemma hcr5_q4_F2_in {A B: Type} (Rr: A -> B -> Prop) l1 l2 x :
  Forall2 Rr l1 l2 -> In x l1 -> exists y, In y l2 /\ Rr x y.
Proof.
  intros HF; induction HF as [| a b l1' l2' Hab HF IH]; simpl; [tauto |].
  intros [-> | Hin]; [exists b; auto |]. destruct (IH Hin) as (y & Hy & Hr). exists y; auto.
Qed.

Lemma hcr5_q4_sfind_nodup {A: Type} (D: list (val * share * A)) a sh E :
  NoDup (saddrs D) -> In (a, sh, E) D -> sfind D a = Some (sh, E).
Proof.
  induction D as [| [[x shx] Ex] D IH]; simpl; [tauto |]. intros Hnd Hin.
  inversion Hnd as [| ? ? Hni Hnd']; subst.
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct Hin as [Heq | Hin]; [congruence |].
    exfalso. apply Hni. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto.
  - destruct Hin as [Heq | Hin]; [congruence | auto].
Qed.

Lemma hcr5_q4_entry_d T a sh E :
  NoDup (saddrs (t_D T)) -> In (a, sh, E) (t_D T) -> t_entry_d T a = E.
Proof.
  intros Hnd Hin. unfold t_entry_d, t_entry. rewrite (hcr5_q4_sfind_nodup _ _ _ _ Hnd Hin). reflexivity.
Qed.

Lemma hcr5_q4_in_saddrs {A: Type} (D: list (val * share * A)) a sh E : In (a, sh, E) D -> In a (saddrs D).
Proof. intros Hin. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto. Qed.

Lemma hcr5_q4_succ_in l a : succ_in l a = nullval \/ In (succ_in l a) l.
Proof.
  induction l as [| x l IH]; cbn; [left; reflexivity |].
  destruct (EqDec_val x a).
  - destruct l as [| y l]; cbn; [left; reflexivity | right; right; left; reflexivity].
  - destruct IH as [-> | H]; [left; reflexivity | right; right; exact H].
Qed.

(* kents_same's precondition: each snapshot kent's entry is in the pool, its peer one of the peers, its link
   NULL or in the table's list *)
Lemma hcr5_q4_kpre L KE NS PS head nb T PS' :
  hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
  map peer_addr4 PS' = map peer_addr4 PS ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS'])) (kent_ptrs T e))
    (map (kent_snapped T) KE).
Proof.
  intros _ (Hke & _) (_ & Hinc & Hnd & _) HPS.
  apply Forall_forall. intros e' He'. apply in_map_iff in He'. destruct He' as (e & <- & He).
  assert (HinK: In (ke_addr e) (hcr5_ka KE)) by (apply in_map, He).
  destruct (hcr5_q4_F2_in _ _ _ _ Hke HinK) as ([[a she] E] & Hy & Hr).
  cbn in Hr. destruct Hr as (Ha & -> & Hpe & _). subst a.
  apply firstn_In in Hy.
  assert (Hs: In (ke_addr e) (saddrs (t_D T))) by (eapply hcr5_q4_in_saddrs; exact Hy).
  assert (HE: t_entry_d T (ke_addr e) = E) by (eapply hcr5_q4_entry_d; eauto).
  assert (Hp: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS']) (e_peer E)).
  { right. apply in_or_app. right. cbn. rewrite app_nil_r, HPS. exact Hpe. }
  assert (Hn: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS']) (succ_in (t_L T) (ke_addr e))).
  { destruct (hcr5_q4_succ_in (t_L T) (ke_addr e)) as [-> | Hi]; [left; reflexivity |].
    right. apply in_or_app. left. apply Hinc. exact Hi. }
  unfold kent_snapped, kent_ptrs; cbn. rewrite HE.
  split; [exact Hs | split; [discriminate |]].
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

(* dev_same's precondition: D = A's device (d_dev NULL, cc_dev wa, tables pta / ita), head = NULL or the first
   peer *)
Lemma hcr5_q4_head_in head (PS: list (val * share * peer)) :
  pk_chain head PS -> head = nullval \/ In head (map peer_addr4 PS).
Proof.
  destruct PS as [| [[a sh] P] PS]; cbn; intros Hc; [left; exact Hc |].
  right. left. destruct Hc as [-> _]. reflexivity.
Qed.

Lemma hcr5_q4_dpre (x25519: list byte -> list byte -> list byte) R L head T (PS PS': list (val * share * peer)) :
  pk_chain head PS -> map peer_addr4 PS' = map peer_addr4 PS ->
  Forall (vp_ok ([l_wa L; d_ptab (hcr5_DAL x25519 R L)] ++
                 vobjs_addrs [VItab Tsh (l_ita L) T; VPeers PS']))
    (dev_ptrs (hcr5_DAL x25519 R L) head (hcr5_DAL x25519 R L) head).
Proof.
  intros Hc HPS.
  assert (Hh: vp_ok ([l_wa L; l_pta L] ++ vobjs_addrs [VItab Tsh (l_ita L) T; VPeers PS']) head).
  { destruct (hcr5_q4_head_in head PS Hc) as [Hh | Hh]; [left; exact Hh |]. right.
    cbn. right. right. right. apply in_or_app. right. rewrite app_nil_r, HPS. exact Hh. }
  unfold hcr5_DAL, hcr5_DA, setup_dev, dev_ptrs; cbn [d_dev d_cc cc_dev d_ptab d_itab].
  repeat (apply Forall_cons; [first [exact Hh | left; reflexivity | right; cbn; tauto] |]).
  apply Forall_nil.
Qed.

(* the table's first entry is NULL or a pool entry (a kent's or a peer's handshake entry): a pointer *)
Lemma hcr5_q4_f2r {A B: Type} (P: A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> Forall (fun y => exists x, In x l1 /\ P x y) l2.
Proof.
  induction 1; constructor.
  - exists x. split; [left; reflexivity | assumption].
  - eapply Forall_impl; [| exact IHForall2]. intros b (a & Ha & Hp). exists a. split; [right |]; assumption.
Qed.

Lemma hcr5_q4_pptrs L KA PS : Forall (hcr5_pok L KA) PS -> Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  intros H. eapply Forall_impl; [| exact H]. intros [[a sh] P] (_ & Ha & _). exact Ha.
Qed.

Lemma hcr5_q4_hd_pn L KE NS PS head nb T :
  hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
  Forall (fun e => isptr (ke_addr e)) KE ->
  is_pointer_or_null (hd nullval (t_L T)).
Proof.
  intros (Hpok & _) (Hke & Hhs) (_ & Hinc & _) Hk.
  pose proof (hcr5_q4_pptrs _ _ _ Hpok) as Hp.
  destruct (t_L T) as [| v l] eqn:E; cbn; [reflexivity|].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv. apply in_map_iff in Hv. destruct Hv as ([[a sh] D] & Ha & Hin). cbn in Ha. subst a.
  rewrite <- (firstn_skipn (length (hcr5_ka KE)) (t_D T)) in Hin. apply in_app_or in Hin.
  rewrite Forall_forall in Hp, Hk. destruct Hin as [Hin | Hin].
  - apply hcr5_q4_f2r in Hke. rewrite Forall_forall in Hke. destruct (Hke _ Hin) as (k & Hk' & -> & _).
    unfold hcr5_ka in Hk'. apply in_map_iff in Hk'. destruct Hk' as (e & <- & He). specialize (Hk _ He).
    destruct (ke_addr e); try contradiction; exact I.
  - apply hcr5_q4_f2r in Hhs. rewrite Forall_forall in Hhs. destruct (Hhs _ Hin) as ([[p shp] P] & HP & -> & _).
    specialize (Hp _ HP). cbn in Hp. unfold hs_addr. destruct p; try contradiction; exact I.
Qed.

(* `head0 == ita.head` (cast to bool) of a pointer or NULL with itself *)
Lemma hcr5_q4_cmp_self v : is_pointer_or_null v ->
  force_val (sem_cast tint tbool (force_val (sem_cmp_pp Ceq v v))) = Vint Int.one.
Proof.
  intros H. destruct v; try contradiction.
  - cbn in H. subst. reflexivity.
  - unfold sem_cmp_pp, Val.cmplu_bool; cbn. rewrite if_true by reflexivity.
    rewrite Ptrofs.eq_true. reflexivity.
Qed.
