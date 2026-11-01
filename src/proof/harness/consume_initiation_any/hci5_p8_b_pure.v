(* law consume_initiation_any, phase P8, segment b: helpers -
   the comparisons dev_same / kents_same / shim_same of unchanged objects are true (reflexivity of the eqb's), and
   their pointer preconditions (lent objects VO = [VItab ..; VPeers PS']) from hci5_inv.  Port of hcr5_q4_pure.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require WgNoise.harness.x_consume_initiation_any.code.

Local Open Scope Z_scope.

(* ---- reflexivity of the comparisons ---- *)
Lemma hci5_p8_b_veqb x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hci5_p8_b_bytes A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

Lemma hci5_p8_b_dev_refl D h : dev_eqb D h D h = true.
Proof.
  unfold dev_eqb. rewrite !hci5_p8_b_veqb, !hci5_p8_b_bytes, !Bool.eqb_reflx, !Int64.eq_true. reflexivity.
Qed.

Lemma hci5_p8_b_shim_refl S w : shim_eqb S w S w = true.
Proof. unfold shim_eqb, warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity. Qed.

Lemma hci5_p8_b_int64s l : int64s_eqb l l = true.
Proof. induction l as [| x l IH]; cbn; [reflexivity | rewrite Int64.eq_true, IH; reflexivity]. Qed.

Lemma hci5_p8_b_symkey A : symkey_eqb A A = true.
Proof. unfold symkey_eqb. rewrite hci5_p8_b_bytes, Int64.eq_true, Bool.eqb_reflx. reflexivity. Qed.

Lemma hci5_p8_b_kp K : kp_eqb K K = true.
Proof.
  unfold kp_eqb. rewrite !hci5_p8_b_symkey, !Int64.eq_true, !Int.eq_true, Bool.eqb_reflx, hci5_p8_b_int64s.
  reflexivity.
Qed.

Lemma hci5_p8_b_entry E : entry_eqb E E = true.
Proof. unfold entry_eqb. destruct (eq_dec (e_peer E) (e_peer E)); [| congruence]. rewrite !Int.eq_true. reflexivity. Qed.

Lemma hci5_p8_b_kents_refl T KE : forallb (kent_same T) (map (kent_snapped T) KE) = true.
Proof.
  induction KE as [| e KE IH]; [reflexivity |]. cbn [map forallb]. rewrite IH, andb_true_r.
  unfold kent_same, kent_snapped, kent_eqb_cur, kent_eqb_nn; cbn.
  rewrite hci5_p8_b_entry, Bool.eqb_reflx, hci5_p8_b_kp, hci5_p8_b_veqb. reflexivity.
Qed.

(* ---- the peers after the call: same addresses and shares ---- *)
Lemma hci5_p8_b_supd_addrs (PS: list (val * share * peer)) a P' :
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [| [[x sh] Q] PS IH]; cbn; [reflexivity |].
  destruct (EqDec_val x a); cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hci5_p8_b_after_addrs PS res : map peer_addr4 (peers_after PS res) = map peer_addr4 PS.
Proof. destruct res as [[a P'] |]; cbn; [apply hci5_p8_b_supd_addrs | reflexivity]. Qed.

Lemma hci5_p8_b_supd_sh (PS: list (val * share * peer)) a P' (Q: share -> Prop) :
  Forall (fun x : val * share * peer => match x with (_, sh, _) => Q sh end) PS ->
  Forall (fun x : val * share * peer => match x with (_, sh, _) => Q sh end) (supd PS a P').
Proof.
  induction PS as [| [[x sh] P] PS IH]; cbn; intros H; [constructor |].
  inversion H; subst. destruct (EqDec_val x a); constructor; auto.
Qed.

Lemma hci5_p8_b_after_ok x25519 R L PS res :
  Forall (hci5_pok x25519 R L) PS -> vobj_ok (VPeers (peers_after PS res)).
Proof.
  intros H. cbn.
  assert (H': Forall (fun x : val * share * peer => match x with (_, sh, _) => readable_share sh end) PS).
  { eapply Forall_impl; [| exact H]. intros [[a sh] P] (-> & _). apply writable_readable, writable_Ews. }
  destruct res as [[a P'] |]; cbn; [apply hci5_p8_b_supd_sh |]; exact H'.
Qed.

(* ---- kents_same's precondition ---- *)
Lemma hci5_p8_b_succ_in l a : succ_in l a = nullval \/ In (succ_in l a) l.
Proof.
  induction l as [| x l IH]; cbn; [left; reflexivity |].
  destruct (EqDec_val x a).
  - destruct l as [| y l]; cbn; [left; reflexivity | right; right; left; reflexivity].
  - destruct IH as [-> | H]; [left; reflexivity | right; right; exact H].
Qed.

Lemma hci5_p8_b_kpre PS KE T PS' :
  hci5_T_ok PS KE T -> itable_wf T -> map peer_addr4 PS' = map peer_addr4 PS ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS'])) (kent_ptrs T e))
    (map (kent_snapped T) KE).
Proof.
  intros (Hs & _ & _ & Hke) (_ & Hinc & _ & _) HPS.
  apply Forall_forall. intros e' He'. apply in_map_iff in He'. destruct He' as (e & <- & He).
  assert (HinS: In (ke_addr e) (saddrs (t_D T))) by (rewrite Hs; apply in_or_app; left; apply in_map, He).
  rewrite Forall_forall in Hke. specialize (Hke _ He).
  assert (Hp: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS']) (e_peer (t_entry_d T (ke_addr e)))).
  { right. apply in_or_app. right. cbn. rewrite app_nil_r, HPS. exact Hke. }
  assert (Hn: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS']) (succ_in (t_L T) (ke_addr e))).
  { destruct (hci5_p8_b_succ_in (t_L T) (ke_addr e)) as [-> | Hi]; [left; reflexivity |].
    right. apply in_or_app. left. apply Hinc. exact Hi. }
  unfold kent_snapped, kent_ptrs; cbn.
  split; [exact HinS | split; [discriminate |]].
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

(* ---- dev_same's precondition: D = B's device (d_dev NULL, cc_dev wb, tables ptb / itb), head NULL or the
   first peer ---- *)
Lemma hci5_p8_b_head_in head (PS: list (val * share * peer)) :
  pk_chain head PS -> head = nullval \/ In head (map peer_addr4 PS).
Proof.
  destruct PS as [| [[a sh] P] PS]; cbn; intros Hc; [left; exact Hc |].
  right. left. destruct Hc as [-> _]. reflexivity.
Qed.

Lemma hci5_p8_b_dpre (x25519: list byte -> list byte -> list byte) R L head T (PS PS': list (val * share * peer)) :
  pk_chain head PS -> map peer_addr4 PS' = map peer_addr4 PS ->
  Forall (vp_ok ([l_wb L; d_ptab (hci5_DB x25519 R L)] ++
                 vobjs_addrs [VItab Tsh (l_itb L) T; VPeers PS']))
    (dev_ptrs (hci5_DB x25519 R L) head (hci5_DB x25519 R L) head).
Proof.
  intros Hc HPS.
  assert (Hh: vp_ok ([l_wb L; l_ptb L] ++ vobjs_addrs [VItab Tsh (l_itb L) T; VPeers PS']) head).
  { destruct (hci5_p8_b_head_in head PS Hc) as [Hh | Hh]; [left; exact Hh |]. right.
    cbn. right. right. right. apply in_or_app. right. rewrite app_nil_r, HPS. exact Hh. }
  unfold hci5_DB, setup_dev, dev_ptrs; cbn [d_dev d_cc cc_dev d_ptab d_itab].
  repeat (apply Forall_cons; [first [exact Hh | left; reflexivity | right; cbn; tauto] |]).
  apply Forall_nil.
Qed.

(* `itb.head == head0` (cast to bool) of a pointer or NULL with itself *)
Lemma hci5_p8_b_cmp_self v : is_pointer_or_null v ->
  force_val (sem_cast tint tbool (force_val (sem_cmp_pp Ceq v v))) = Vint Int.one.
Proof.
  intros H. destruct v; try contradiction.
  - cbn in H. subst. reflexivity.
  - unfold sem_cmp_pp, Val.cmplu_bool; cbn. rewrite if_true by reflexivity.
    rewrite Ptrofs.eq_true. reflexivity.
Qed.
