(* law cookie_reply, phase P12, segment Y: pure helpers - the comparisons
   dev_same / kents_same / shim_same of unchanged objects are true (reflexivity of the eqb's), and their
   pointer preconditions (lent objects VO = [VItab ..; VPeers PS']) from the state's invariants.
   Port of consume_response_any's hcr5_q4_pure.v. *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.

Local Open Scope Z_scope.

(* ---- reflexivity of the comparisons ---- *)
Lemma hcy5_p12_y_veqb x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hcy5_p12_y_bytes A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

Lemma hcy5_p12_y_dev_refl D h : dev_eqb D h D h = true.
Proof.
  unfold dev_eqb. rewrite !hcy5_p12_y_veqb, !hcy5_p12_y_bytes, !Bool.eqb_reflx, !Int64.eq_true. reflexivity.
Qed.

Lemma hcy5_p12_y_shim_refl S w : shim_eqb S w S w = true.
Proof. unfold shim_eqb, warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity. Qed.

Lemma hcy5_p12_y_int64s l : int64s_eqb l l = true.
Proof. induction l as [| x l IH]; cbn; [reflexivity | rewrite Int64.eq_true, IH; reflexivity]. Qed.

Lemma hcy5_p12_y_symkey A : symkey_eqb A A = true.
Proof. unfold symkey_eqb. rewrite hcy5_p12_y_bytes, Int64.eq_true, Bool.eqb_reflx. reflexivity. Qed.

Lemma hcy5_p12_y_kp K : kp_eqb K K = true.
Proof.
  unfold kp_eqb. rewrite !hcy5_p12_y_symkey, !Int64.eq_true, !Int.eq_true, Bool.eqb_reflx, hcy5_p12_y_int64s.
  reflexivity.
Qed.

Lemma hcy5_p12_y_entry E : entry_eqb E E = true.
Proof. unfold entry_eqb. destruct (eq_dec (e_peer E) (e_peer E)); [| congruence]. rewrite !Int.eq_true. reflexivity. Qed.

Lemma hcy5_p12_y_kents_refl T KE : forallb (kent_same T) (map (kent_snapped T) KE) = true.
Proof.
  induction KE as [| e KE IH]; [reflexivity |]. cbn [map forallb]. rewrite IH, andb_true_r.
  unfold kent_same, kent_snapped, kent_eqb_cur, kent_eqb_nn; cbn.
  rewrite hcy5_p12_y_entry, Bool.eqb_reflx, hcy5_p12_y_kp, hcy5_p12_y_veqb. reflexivity.
Qed.

(* ---- the peers after the consumption: same addresses and shares ---- *)
Lemma hcy5_p12_y_supd_addrs (PS: list (val * share * peer)) a P' :
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [| [[x sh] Q] PS IH]; cbn; [reflexivity |].
  destruct (EqDec_val x a); cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hcy5_p12_y_after_addrs PS res : map peer_addr4 (peers_after PS res) = map peer_addr4 PS.
Proof. destruct res as [[a P'] |]; cbn; [apply hcy5_p12_y_supd_addrs | reflexivity]. Qed.

Lemma hcy5_p12_y_phead_after PS res : hcy5_phead (peers_after PS res) = hcy5_phead PS.
Proof.
  destruct res as [[a P'] |]; cbn; [| reflexivity].
  destruct PS as [| [[x sh] Q] PS]; cbn; [reflexivity |].
  destruct (EqDec_val x a); reflexivity.
Qed.

Lemma hcy5_p12_y_supd_sh (PS: list (val * share * peer)) a P' (Q: share -> Prop) :
  Forall (fun x : val * share * peer => match x with (_, sh, _) => Q sh end) PS ->
  Forall (fun x : val * share * peer => match x with (_, sh, _) => Q sh end) (supd PS a P').
Proof.
  induction PS as [| [[x sh] P] PS IH]; cbn; intros H; [constructor |].
  inversion H; subst. destruct (EqDec_val x a); constructor; auto.
Qed.

Lemma hcy5_p12_y_after_ok L KA PS res :
  Forall (hcy5_pok L KA) PS -> vobj_ok (VPeers (peers_after PS res)).
Proof.
  intros H. cbn.
  assert (H': Forall (fun x : val * share * peer => match x with (_, sh, _) => readable_share sh end) PS).
  { eapply Forall_impl; [| exact H]. intros [[a sh] P] (-> & _). apply writable_readable, writable_Ews. }
  destruct res as [[a P'] |]; cbn; [apply hcy5_p12_y_supd_sh |]; exact H'.
Qed.

(* ---- pure table facts ---- *)
Lemma hcy5_p12_y_sfind_nodup {A: Type} (D: list (val * share * A)) a sh E :
  NoDup (saddrs D) -> In (a, sh, E) D -> sfind D a = Some (sh, E).
Proof.
  induction D as [| [[x shx] Ex] D IH]; simpl; [tauto |]. intros Hnd Hin.
  inversion Hnd as [| ? ? Hni Hnd']; subst.
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct Hin as [Heq | Hin]; [congruence |].
    exfalso. apply Hni. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto.
  - destruct Hin as [Heq | Hin]; [congruence | auto].
Qed.

Lemma hcy5_p12_y_entry_d T a sh E :
  NoDup (saddrs (t_D T)) -> In (a, sh, E) (t_D T) -> t_entry_d T a = E.
Proof.
  intros Hnd Hin. unfold t_entry_d, t_entry. rewrite (hcy5_p12_y_sfind_nodup _ _ _ _ Hnd Hin). reflexivity.
Qed.

Lemma hcy5_p12_y_in_saddrs {A: Type} (D: list (val * share * A)) a sh E : In (a, sh, E) D -> In a (saddrs D).
Proof. intros Hin. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto. Qed.

Lemma hcy5_p12_y_succ_in l a : succ_in l a = nullval \/ In (succ_in l a) l.
Proof.
  induction l as [| x l IH]; cbn; [left; reflexivity |].
  destruct (EqDec_val x a).
  - destruct l as [| y l]; cbn; [left; reflexivity | right; right; left; reflexivity].
  - destruct IH as [-> | H]; [left; reflexivity | right; right; exact H].
Qed.

(* kents_same's precondition: each snapshot kent's entry is in the pool, its peer one of the peers, its link
   NULL or in the table's list *)
Lemma hcy5_p12_y_kpre (PS: list (val * share * peer)) KE T PS' :
  hcy5_T_ok PS KE T -> itable_wf T -> map peer_addr4 PS' = map peer_addr4 PS ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS'])) (kent_ptrs T e))
    (map (kent_snapped T) KE).
Proof.
  intros ((own & ix & HD & Hown) & _) (_ & Hinc & Hnd & _) HPS.
  apply Forall_forall. intros e' He'. apply in_map_iff in He'. destruct He' as (e & <- & He).
  assert (HinK: In (ke_addr e) (map ke_addr KE)) by (apply in_map, He).
  assert (Hy: In (hcy5_kentry own ix (ke_addr e)) (t_D T)).
  { rewrite HD. apply in_or_app. left. apply in_map, HinK. }
  unfold hcy5_kentry in Hy.
  assert (Hs: In (ke_addr e) (saddrs (t_D T))) by (eapply hcy5_p12_y_in_saddrs; exact Hy).
  assert (HE: t_entry_d T (ke_addr e) = mkEntry (own (ke_addr e)) IDX_KEYPAIR (ix (ke_addr e)))
    by (eapply hcy5_p12_y_entry_d; eauto).
  rewrite Forall_forall in Hown. specialize (Hown _ HinK).
  assert (Hp: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS']) (own (ke_addr e))).
  { right. apply in_or_app. right. cbn. rewrite app_nil_r, HPS. exact Hown. }
  assert (Hn: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS']) (succ_in (t_L T) (ke_addr e))).
  { destruct (hcy5_p12_y_succ_in (t_L T) (ke_addr e)) as [-> | Hi]; [left; reflexivity |].
    right. apply in_or_app. left. apply Hinc. exact Hi. }
  unfold kent_snapped, kent_ptrs; cbn. rewrite HE. cbn [e_peer].
  split; [exact Hs | split; [discriminate |]].
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

(* dev_same's precondition: D = A's device (d_dev NULL, cc_dev wa, tables pta / ita), heads = NULL or the
   first peer *)
Lemma hcy5_p12_y_phead_in (PS: list (val * share * peer)) :
  hcy5_phead PS = nullval \/ In (hcy5_phead PS) (map peer_addr4 PS).
Proof.
  destruct PS as [| [[a sh] P] PS]; cbn; [left; reflexivity | right; left; reflexivity].
Qed.

Lemma hcy5_p12_y_dpre (x25519: list byte -> list byte -> list byte) R L T (PS PS': list (val * share * peer)) :
  map peer_addr4 PS' = map peer_addr4 PS -> hcy5_phead PS' = hcy5_phead PS ->
  Forall (vp_ok ([l_wa L; d_ptab (hcy5_DA x25519 R L)] ++
                 vobjs_addrs [VItab Tsh (l_ita L) T; VPeers PS']))
    (dev_ptrs (hcy5_DA x25519 R L) (hcy5_phead PS) (hcy5_DA x25519 R L) (hcy5_phead PS')).
Proof.
  intros HPS Hh'. rewrite Hh'.
  assert (Hh: vp_ok ([l_wa L; l_pta L] ++ vobjs_addrs [VItab Tsh (l_ita L) T; VPeers PS']) (hcy5_phead PS)).
  { destruct (hcy5_p12_y_phead_in PS) as [Hh | Hh]; [left; exact Hh |]. right.
    cbn. right. right. right. apply in_or_app. right. rewrite app_nil_r, HPS. exact Hh. }
  unfold hcy5_DA, setup_dev, dev_ptrs; cbn [d_dev d_cc cc_dev d_ptab d_itab].
  repeat (apply Forall_cons; [first [exact Hh | left; reflexivity | right; cbn; tauto] |]).
  apply Forall_nil.
Qed.

(* `ita.head == head0` (cast to bool) of a pointer or NULL with itself *)
Lemma hcy5_p12_y_cmp_self v : is_pointer_or_null v ->
  force_val (sem_cast tint tbool (force_val (sem_cmp_pp Ceq v v))) = Vint Int.one.
Proof.
  intros H. destruct v; try contradiction.
  - cbn in H. subst. reflexivity.
  - unfold sem_cmp_pp, Val.cmplu_bool; cbn. rewrite if_true by reflexivity.
    rewrite Ptrofs.eq_true. reflexivity.
Qed.
