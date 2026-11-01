(* law cookie_mac, phase P7b: helpers for the frame CHECKs (P5c, P7b):
   - reflexivity of the comparisons (snap_eqb, pr_eqb_nc, pr_eqb, dev_eqb, shim_eqb, kent_same of snapped kents);
   - the pointer preconditions of hs_same4 / pr_same(_but_cookie)4 / dev_same4 / kents_same4 with lent objects VO,
     from hck5_aok;
   - separation-logic glue: p whole (hck5_prest + cookie_rep), its reference count field, B whole (hck5_drest +
     checker_rep), the index table's head at the world, the lent-object lists. *)
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
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require WgNoise.harness.x_cookie_mac.code.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* reflexivity of the comparisons                                          *)
(* ---------------------------------------------------------------------- *)

Lemma hck5_p7b_veqb x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hck5_p7b_bytes A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

Lemma hck5_p7b_dev_refl D h : dev_eqb D h D h = true.
Proof.
  unfold dev_eqb. rewrite !hck5_p7b_veqb, !hck5_p7b_bytes, !Bool.eqb_reflx, !Int64.eq_true. reflexivity.
Qed.

Lemma hck5_p7b_shim_refl S w : shim_eqb S w S w = true.
Proof. unfold shim_eqb, warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity. Qed.

Lemma hck5_p7b_int64s l : int64s_eqb l l = true.
Proof. induction l as [| x l IH]; cbn; [reflexivity | rewrite Int64.eq_true, IH; reflexivity]. Qed.

Lemma hck5_p7b_symkey A : symkey_eqb A A = true.
Proof. unfold symkey_eqb. rewrite hck5_p7b_bytes, Int64.eq_true, Bool.eqb_reflx. reflexivity. Qed.

Lemma hck5_p7b_kp K : kp_eqb K K = true.
Proof.
  unfold kp_eqb. rewrite !hck5_p7b_symkey, !Int64.eq_true, !Int.eq_true, Bool.eqb_reflx, hck5_p7b_int64s.
  reflexivity.
Qed.

Lemma hck5_p7b_entry E : entry_eqb E E = true.
Proof. unfold entry_eqb. destruct (eq_dec (e_peer E) (e_peer E)); [| congruence]. rewrite !Int.eq_true. reflexivity. Qed.

Lemma hck5_p7b_hs H : hs_eqb H H = true.
Proof.
  unfold hs_eqb. rewrite !Int.eq_true, !Int64.eq_true, !hck5_p7b_bytes.
  destruct (eq_dec (hs_sid H) (hs_sid H)); [reflexivity | congruence].
Qed.

Lemma hck5_p7b_snap s : snap_eqb s s = true.
Proof.
  unfold snap_eqb. rewrite hck5_p7b_entry, hck5_p7b_hs, Bool.eqb_reflx.
  destruct (eq_dec (sn_next s) (sn_next s)); [reflexivity | congruence].
Qed.

(* hs_same of p's handshake snapshot, p's cookie changed since *)
Lemma hck5_p7b_snap_cur T p P C : snap_eqb (hs_snap_cur T p P) (hs_snap_cur T p (p_set_cookie P C)) = true.
Proof. apply hck5_p7b_snap. Qed.

Lemma hck5_p7b_cookie C : cookie_eqb C C = true.
Proof. unfold cookie_eqb. rewrite !Int64.eq_true, !Bool.eqb_reflx, !hck5_p7b_bytes. reflexivity. Qed.

Lemma hck5_p7b_pr_nc_refl P : pr_eqb_nc P P = true.
Proof. unfold pr_eqb_nc. rewrite !hck5_p7b_veqb, Bool.eqb_reflx, !Int64.eq_true. reflexivity. Qed.

(* pr_same_but_cookie of p whole with its cookie C, p's cookie now C' *)
Lemma hck5_p7b_pr_nc P C C' : pr_eqb_nc (p_set_cookie P C) (p_set_cookie P C') = true.
Proof. apply (hck5_p7b_pr_nc_refl (p_set_cookie P C)). Qed.

Lemma hck5_p7b_pr_refl P : pr_eqb P P = true.
Proof. unfold pr_eqb. rewrite hck5_p7b_pr_nc_refl, hck5_p7b_cookie. reflexivity. Qed.

Lemma hck5_p7b_kents_refl T KE :
  Forall (fun e => kent_snapped T e = e) KE -> forallb (kent_same T) KE = true.
Proof.
  induction KE as [| e KE IH]; intros HF; [reflexivity |].
  inversion HF as [| ? ? He HF']; subst. cbn [forallb]. rewrite IH by exact HF'. rewrite andb_true_r.
  rewrite <- He.
  unfold kent_same, kent_snapped, kent_eqb_cur, kent_eqb_nn; cbn.
  rewrite hck5_p7b_entry, Bool.eqb_reflx, hck5_p7b_kp, hck5_p7b_veqb. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* pure table facts                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hck5_p7b_entry_peer (D: list (val * share * entry)) a p :
  In a (saddrs D) -> Forall (fun x => e_peer (snd x) = p) D ->
  match sfind D a with Some (_, E) => e_peer E = p | None => False end.
Proof.
  induction D as [| [[x sh] E] D IH]; simpl; [tauto |].
  intros HI HF. inversion HF as [| ? ? H1 H2]; clear HF.
  destruct (EqDec_val x a); [exact H1 |].
  apply IH; auto. destruct HI; [congruence | auto].
Qed.

(* every pool entry's peer is p *)
Lemma hck5_p7b_entry_d T a p :
  In a (saddrs (t_D T)) -> Forall (fun x => e_peer (snd x) = p) (t_D T) ->
  e_peer (t_entry_d T a) = p.
Proof.
  intros HI HF. pose proof (hck5_p7b_entry_peer _ _ _ HI HF) as H.
  unfold t_entry_d, t_entry. destruct (sfind (t_D T) a) as [[? E]|]; [exact H | contradiction].
Qed.

Lemma hck5_p7b_succ_in l a : succ_in l a = nullval \/ In (succ_in l a) l.
Proof.
  induction l as [| x l IH]; cbn; [left; reflexivity |].
  destruct (EqDec_val x a).
  - destruct l as [| y l]; cbn; [left; reflexivity | right; right; left; reflexivity].
  - destruct IH as [-> | H]; [left; reflexivity | right; right; exact H].
Qed.

(* a link of the table's list: NULL or a pool address *)
Lemma hck5_p7b_succ_ok T a own : itable_wf T -> incl (saddrs (t_D T)) own -> vp_ok own (succ_in (t_L T) a).
Proof.
  intros (_ & Hinc & _) Ho. destruct (hck5_p7b_succ_in (t_L T) a) as [-> | Hi]; [left; reflexivity |].
  right. apply Ho, Hinc, Hi.
Qed.

Lemma hck5_p7b_hs_in L A : hck5_aok L A -> In (hs_addr (l_p L)) (saddrs (t_D (a_T A))).
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hsad & _). rewrite Hsad. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma hck5_p7b_ke_in L A e : hck5_aok L A -> In e (a_KE A) -> In (ke_addr e) (saddrs (t_D (a_T A))).
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hsad & _) He. rewrite Hsad. apply in_app_iff. left. apply in_map, He.
Qed.

(* ---------------------------------------------------------------------- *)
(* the pointer preconditions with lent objects                             *)
(* ---------------------------------------------------------------------- *)

(* hs_same(&hs0, &p.handshake): the lent objects hold wa's identity *)
Lemma hck5_p7b_hs_pre L A C VO :
  hck5_aok L A -> itable_wf (a_T A) -> In (id_addr (l_wa L)) (vobjs_addrs VO) ->
  Forall (vp_ok (hs_own (l_p L) (a_T A) VO))
    (hs_ptrs (hs_snap_cur (a_T A) (l_p L) (a_P A)) (hs_snap_cur (a_T A) (l_p L) (p_set_cookie (a_P A) C))).
Proof.
  intros Hok Hwf Hid. pose proof (hck5_p7b_hs_in L A Hok) as Hin.
  destruct Hok as (_ & _ & _ & Hsid & _ & _ & _ & _ & Hpeer & _).
  assert (Hn: vp_ok (hs_own (l_p L) (a_T A) VO) (succ_in (t_L (a_T A)) (hs_addr (l_p L)))).
  { apply hck5_p7b_succ_ok; [exact Hwf |]. intros x Hx. right. apply in_or_app. left. exact Hx. }
  assert (Hp: vp_ok (hs_own (l_p L) (a_T A) VO) (e_peer (t_entry_d (a_T A) (hs_addr (l_p L))))).
  { rewrite (hck5_p7b_entry_d _ _ (l_p L) Hin Hpeer). right. left. reflexivity. }
  assert (Hs: vp_ok (hs_own (l_p L) (a_T A) VO) (hs_sid (p_hs (a_P A)))).
  { rewrite Hsid. right. right. apply in_or_app. right. exact Hid. }
  unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of; cbn [sn_next sn_entry sn_hs p_hs p_set_cookie].
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

(* pr_same(_but_cookie)(&ps0, &p): the lent objects hold wa and the kents *)
Lemma hck5_p7b_pr_pre L A C C' VO :
  hck5_aok L A -> In (l_wa L) (vobjs_addrs VO) -> incl (map ke_addr (a_KE A)) (vobjs_addrs VO) ->
  Forall (vp_ok (l_p L :: vobjs_addrs VO)) (pr_ptrs (p_set_cookie (a_P A) C) (p_set_cookie (a_P A) C')).
Proof.
  intros (_ & Hdev & Hpk & _ & Hslots & _) Hwa Hke.
  assert (Hd: vp_ok (l_p L :: vobjs_addrs VO) (p_device (a_P A))) by (rewrite Hdev; right; right; exact Hwa).
  assert (Hk: vp_ok (l_p L :: vobjs_addrs VO) (p_pknext (a_P A))) by (rewrite Hpk; left; reflexivity).
  assert (Hs: forall v, v = nullval \/ In v (map ke_addr (a_KE A)) -> vp_ok (l_p L :: vobjs_addrs VO) v).
  { intros v [-> | Hv]; [left; reflexivity | right; right; apply Hke, Hv]. }
  inversion Hslots as [| ? ? S1 Hs1]; inversion Hs1 as [| ? ? S2 Hs2]; inversion Hs2 as [| ? ? S3 _].
  apply Hs in S1. apply Hs in S2. apply Hs in S3.
  unfold pr_ptrs; cbn [p_set_cookie p_device p_cur p_prev p_next p_pknext].
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

(* dev_same(&da, &wa): A's device, its public-key table's head p; the lent objects hold ita and p *)
Lemma hck5_p7b_da_pre x25519 R L VO :
  In (l_ita L) (vobjs_addrs VO) -> In (l_p L) (vobjs_addrs VO) ->
  Forall (vp_ok ([l_wa L; d_ptab (hck5_DA x25519 R L)] ++ vobjs_addrs VO))
    (dev_ptrs (hck5_DA x25519 R L) (l_p L) (hck5_DA x25519 R L) (l_p L)).
Proof.
  intros Hi Hp.
  assert (H1: vp_ok ([l_wa L; l_pta L] ++ vobjs_addrs VO) (l_ita L)) by (right; right; right; exact Hi).
  assert (H2: vp_ok ([l_wa L; l_pta L] ++ vobjs_addrs VO) (l_p L)) by (right; right; right; exact Hp).
  assert (H3: vp_ok ([l_wa L; l_pta L] ++ vobjs_addrs VO) (l_wa L)) by (right; left; reflexivity).
  assert (H4: vp_ok ([l_wa L; l_pta L] ++ vobjs_addrs VO) (l_pta L)) by (right; right; left; reflexivity).
  assert (H5: vp_ok ([l_wa L; l_pta L] ++ vobjs_addrs VO) nullval) by (left; reflexivity).
  unfold hck5_DA, setup_dev, dev_ptrs; cbn [d_dev d_cc cc_dev d_ptab d_itab].
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

(* dev_same(&db, &wb): B whole with the checker CC (B's device), an empty public-key table; the lent objects
   hold itb *)
Lemma hck5_p7b_db_pre x25519 R L CC VO :
  cc_dev CC = l_wb L -> In (l_itb L) (vobjs_addrs VO) ->
  Forall (vp_ok ([l_wb L; d_ptab (hck5_DBc x25519 R L CC)] ++ vobjs_addrs VO))
    (dev_ptrs (hck5_DBc x25519 R L CC) nullval (hck5_DBc x25519 R L CC) nullval).
Proof.
  intros Hcc Hi.
  assert (H1: vp_ok ([l_wb L; l_ptb L] ++ vobjs_addrs VO) (l_itb L)) by (right; right; right; exact Hi).
  assert (H3: vp_ok ([l_wb L; l_ptb L] ++ vobjs_addrs VO) (l_wb L)) by (right; left; reflexivity).
  assert (H4: vp_ok ([l_wb L; l_ptb L] ++ vobjs_addrs VO) (l_ptb L)) by (right; right; left; reflexivity).
  assert (H5: vp_ok ([l_wb L; l_ptb L] ++ vobjs_addrs VO) nullval) by (left; reflexivity).
  unfold hck5_DBc, hck5_DB, setup_dev, dev_ptrs; cbn [d_dev d_cc d_ptab d_itab]. rewrite Hcc.
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

Lemma hck5_p7b_cc2_dev x25519 R L now cmode : cc_dev (hck5_CC2 x25519 R L now cmode) = l_wb L.
Proof.
  unfold hck5_CC2, hck5_CC1, hck5_DB, setup_dev. destruct (andb _ _); reflexivity.
Qed.

(* kents_same(kes): every kent snapped, its entry in the pool (peer p), the links NULL or pool entries *)
Lemma hck5_p7b_kents_pre L A VO :
  hck5_aok L A -> itable_wf (a_T A) -> In (l_p L) (vobjs_addrs VO) ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D (a_T A))) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D (a_T A)) ++ vobjs_addrs VO)) (kent_ptrs (a_T A) e)) (a_KE A).
Proof.
  intros Hok Hwf Hp. pose proof Hok as (_ & _ & _ & _ & _ & _ & _ & _ & Hpeer & Hsnap & _).
  apply Forall_forall. intros e He.
  pose proof (hck5_p7b_ke_in L A e Hok He) as Hin.
  rewrite Forall_forall in Hsnap. specialize (Hsnap e He).
  rewrite <- Hsnap. cbn [ke_addr]. unfold kent_snapped at 1; cbn [ke_addr ke_snap].
  split; [unfold kent_snapped; exact Hin | split; [unfold kent_snapped; discriminate |]].
  assert (HP: vp_ok (saddrs (t_D (a_T A)) ++ vobjs_addrs VO) (e_peer (t_entry_d (a_T A) (ke_addr e)))).
  { rewrite (hck5_p7b_entry_d _ _ (l_p L) Hin Hpeer). right. apply in_or_app. right. exact Hp. }
  assert (HN: vp_ok (saddrs (t_D (a_T A)) ++ vobjs_addrs VO) (succ_in (t_L (a_T A)) (ke_addr e))).
  { apply hck5_p7b_succ_ok; [exact Hwf |]. intros x Hx. apply in_or_app. left. exact Hx. }
  unfold kent_ptrs, kent_snapped; cbn [ke_addr ke_snap ks_E ks_next].
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

(* the table's first entry: NULL or a pool entry (a kent's or p's handshake entry), a pointer *)
Lemma hck5_p7b_hd_pn L A :
  hck5_aok L A -> itable_wf (a_T A) -> is_pointer_or_null (hd nullval (t_L (a_T A))).
Proof.
  intros (FC & _ & _ & _ & _ & Hkp & Hsad & _) (_ & Hinc & _).
  destruct (t_L (a_T A)) as [| v l] eqn:E; cbn; [reflexivity |].
  assert (Hv: In v (saddrs (t_D (a_T A)))) by (apply Hinc; left; reflexivity).
  rewrite Hsad in Hv. apply in_app_iff in Hv. destruct Hv as [Hv | [<- | []]].
  - apply list_in_map_inv in Hv. destruct Hv as (e & -> & He).
    rewrite Forall_forall in Hkp. specialize (Hkp e He). destruct (ke_addr e); try contradiction; exact I.
  - destruct FC as (Hp & _). unfold hs_addr. destruct (l_p L); try contradiction; exact I.
Qed.

(* `ita.head == head0` (cast to bool) of a pointer or NULL with itself *)
Lemma hck5_p7b_cmp_self v : is_pointer_or_null v ->
  force_val (sem_cast tint tbool (force_val (sem_cmp_pp Ceq v v))) = Vint Int.one.
Proof.
  intros H. destruct v; try contradiction.
  - cbn in H. subst. reflexivity.
  - unfold sem_cmp_pp, Val.cmplu_bool; cbn. rewrite if_true by reflexivity.
    rewrite Ptrofs.eq_true. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* separation-logic glue                                                   *)
(* ---------------------------------------------------------------------- *)

#[local] Existing Instance W_cookie_mac.

#[local] Instance hck5_p7b_CCE : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.

(* p whole *)
Lemma hck5_p7b_fold sh p P C :
  (hck5_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic = peer_rep sh p (p_set_cookie P C).
Proof.
  unfold hck5_prest, peer_rep. destruct P; simpl. apply pred_ext; Intros; entailer!.
Qed.

Lemma hck5_p7b_fold_d sh p P C :
  (hck5_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic |-- peer_rep sh p (p_set_cookie P C).
Proof. rewrite hck5_p7b_fold. apply derives_refl. Qed.

Lemma hck5_p7b_unfold_d sh p P C :
  peer_rep sh p (p_set_cookie P C) |-- (hck5_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic.
Proof. rewrite hck5_p7b_fold. apply derives_refl. Qed.

(* p's reference count field *)
Lemma hck5_p7b_refs_nest sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at Noise.CS sh t_peer [StructField I._refcount; StructField I._refcount] (Vint v) p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hck5_p7b_refs_conv sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint v) p.
Proof.
  rewrite hck5_p7b_refs_nest.
  change (Tstruct HK._wg_peer noattr) with t_peer. change HK._refcount with I._refcount.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_cookie_mac _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.

(* hck5_prest without the reference count *)
Definition hck5_p7b_prestR (sh: share) (p: val) (P: peer) : mpred :=
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hck5_p7b_open sh p P :
  hck5_prest sh p P =
  (hck5_p7b_prestR sh p P *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint (p_refs P)) p)%logic.
Proof.
  rewrite <- hck5_p7b_refs_conv.
  unfold hck5_prest, hck5_p7b_prestR. apply pred_ext; Intros; entailer!.
Qed.

Lemma hck5_p7b_close sh p P :
  (hck5_p7b_prestR sh p P *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint (p_refs P)) p)%logic
  |-- hck5_prest sh p P.
Proof. rewrite hck5_p7b_open. apply derives_refl. Qed.

(* B whole: hck5_drest and the checker fold into device_rep of hck5_DBc *)
Lemma hck5_p7b_dev_fold x25519 R L CC :
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic =
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC).
Proof.
  unfold hck5_drest, device_rep, hck5_DBc. simpl.
  apply pred_ext; entailer!.
Qed.

Lemma hck5_p7b_dev_in x25519 R L CC :
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic |--
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC).
Proof. rewrite hck5_p7b_dev_fold. apply derives_refl. Qed.

Lemma hck5_p7b_dev_out x25519 R L CC :
  device_rep Tsh (l_wb L) (hck5_DBc x25519 R L CC) |--
  (hck5_drest Tsh (l_wb L) (hck5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC)%logic.
Proof. rewrite hck5_p7b_dev_fold. apply derives_refl. Qed.

(* the index table's head field at the world *)
Lemma hck5_p7b_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_cookie_mac sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_cookie_mac _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hck5_p7b_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W_cookie_mac sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T)))%logic.
Proof. unfold itable. rewrite hck5_p7b_itab_W. reflexivity. Qed.

Lemma hck5_p7b_itable_fold sht tab T : itable_wf T ->
  (@data_at W_cookie_mac sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T)%logic.
Proof. intros HT. rewrite hck5_p7b_itable_open. entailer!. Qed.

(* the table's first entry is a valid pointer (NULL or a pool entry) *)
Lemma hck5_p7b_hd_valid sht tab T : itable sht tab T |-- valid_pointer (hd nullval (t_L T)).
Proof.
  unfold itable. Intros. destruct H as (_ & Hinc & _ & Hw).
  destruct (t_L T) as [| v l] eqn:EL; cbn [hd]; [apply valid_pointer_null |].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv; apply in_map_iff in Hv; destruct Hv as ([[a sh] E] & Ha & Hin); cbn in Ha; subst a.
  rewrite Forall_forall in Hw; specialize (Hw _ Hin); cbn in Hw.
  apply sepcon_valid_pointer2.
  eapply derives_trans; [apply (iter_sepcon_in_true (pool_item_rep (v :: l)) (t_D T) _ Hin) |].
  apply sepcon_valid_pointer1. unfold pool_item_rep, entry_at.
  apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable; auto | simpl; lia].
Qed.

Lemma hck5_p7b_itable_wf sht tab T : itable sht tab T |-- !! itable_wf T.
Proof. unfold itable. entailer!. Qed.

(* lent objects *)
Lemma hck5_p7b_vo1 o : vobj_rep W_cookie_mac o = vobjs W_cookie_mac [o].
Proof. unfold vobjs. cbn [iter_sepcon]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hck5_p7b_vo2 o1 o2 :
  (vobj_rep W_cookie_mac o1 * vobj_rep W_cookie_mac o2)%logic = vobjs W_cookie_mac [o1; o2].
Proof. unfold vobjs. cbn [iter_sepcon]. rewrite sepcon_emp. reflexivity. Qed.
