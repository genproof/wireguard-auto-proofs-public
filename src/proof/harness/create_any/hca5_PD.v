(* law create_any: Segment D = statements 15..20 (kes = kents_add(&ita, NULL, &p, 1); kents_snap(kes); pr_take(&ps, &p); refs0 = p.refcount.refcount; dev_take(&ds, &wa); shim_take(&ss)), from hca5_SB to hca5_SK.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: same C where the C did not change). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

(* the peer p after kents_add's fills (every kent owned by p) *)
Fixpoint hca5_pd_fill (P: peer) (KD: list kdraw) : peer :=
  match KD with [] => P | d :: KD' => fill_slot (hca5_pd_fill P KD') (kd_addr d) (kd_slot d) end.

Lemma hca5_pd_owners p sh P KD :
  kents_draws_ok [(p, sh, P)] KD -> Forall (fun d => kd_owner d = p) KD.
Proof.
  intros [Hf _]. eapply Forall_impl; [| exact Hf].
  intros d [Hin _]. simpl in Hin. destruct Hin as [-> | []]. reflexivity.
Qed.

Lemma hca5_pd_PS p sh P KD :
  Forall (fun d => kd_owner d = p) KD -> kents_PS true [(p, sh, P)] KD = [(p, sh, hca5_pd_fill P KD)].
Proof.
  induction KD as [| d KD IH]; intros Ho; [reflexivity |].
  inversion Ho as [| ? ? Hd Ho']; subst. simpl. rewrite IH by exact Ho'.
  unfold fill_peers. simpl. destruct (EqDec_val (kd_owner d) (kd_owner d)); [reflexivity | congruence].
Qed.

Lemma hca5_pd_fill_fields P KD :
  p_device (hca5_pd_fill P KD) = p_device P /\ p_hs (hca5_pd_fill P KD) = p_hs P /\
  p_pknext (hca5_pd_fill P KD) = p_pknext P /\ p_refs (hca5_pd_fill P KD) = p_refs P.
Proof.
  induction KD as [| d KD IH]; [auto |]. simpl.
  destruct IH as (H1 & H2 & H3 & H4).
  unfold fill_slot; repeat first [destruct (Z.eq_dec _ _) | destruct (eq_dec _ _)];
    unfold p_set_slots; simpl; auto.
Qed.

Lemma hca5_pd_pok_step L P ks k c :
  hca5_pok L P ks -> hca5_pok L (fill_slot P k c) (k :: ks).
Proof.
  intros (Hd & Hs & Hok & Hpk & Hsl).
  assert (Hsl': Forall (fun v => v = nullval \/ In v (k :: ks)) [p_cur P; p_prev P; p_next P]).
  { eapply Forall_impl; [| exact Hsl]. intros v [? | ?]; [left | right; right]; auto. }
  inversion Hsl' as [| ? ? Hc Hsl1]; subst; inversion Hsl1 as [| ? ? Hp Hsl2]; subst;
    inversion Hsl2 as [| ? ? Hn _]; subst.
  assert (Hk: k = nullval \/ In k (k :: ks)) by (right; left; reflexivity).
  unfold fill_slot; repeat first [destruct (Z.eq_dec _ _) | destruct (eq_dec _ _)];
    unfold hca5_pok, p_set_slots; simpl;
    refine (conj Hd (conj Hs (conj Hok (conj Hpk _)))); repeat (apply Forall_cons; [assumption |]); apply Forall_nil.
Qed.

Lemma hca5_pd_pok L P KD :
  hca5_pok L P [] -> hca5_pok L (hca5_pd_fill P KD) (map kd_addr KD).
Proof.
  intros H. induction KD as [| d KD IH]; [exact H |]. simpl. apply hca5_pd_pok_step, IH.
Qed.

Lemma hca5_pd_vremove_in a x l : In x l -> x <> a -> In x (vremove a l).
Proof.
  induction l as [| y l IH]; simpl; [tauto |].
  intros [-> | Hin] Hne.
  - destruct (EqDec_val x a); [congruence |]. simpl; left; reflexivity.
  - destruct (EqDec_val y a); [auto | simpl; right; auto].
Qed.

Lemma hca5_pd_ins_eq T a sh E idx :
  t_insert (t_add T a sh E) a idx =
  mkT ((a, sh, mkEntry (e_peer E) (e_type E) idx) :: t_D T) (a :: vremove a (t_L T)).
Proof.
  unfold t_insert, t_set_index, t_entry, t_add, t_upd. simpl.
  destruct (EqDec_val a a); [| congruence]. simpl.
  destruct (EqDec_val a a); [| congruence]. reflexivity.
Qed.

Lemma hca5_pd_TD p T KD :
  Forall (fun d => kd_owner d = p) KD -> t_D (kents_T T KD) = map (hca5_kpool p) KD ++ t_D T.
Proof.
  induction KD as [| d KD IH]; intros Ho; [reflexivity |].
  inversion Ho as [| ? ? Hd Ho']; subst. simpl kents_T. rewrite hca5_pd_ins_eq. simpl.
  rewrite IH by exact Ho'. reflexivity.
Qed.

Lemma hca5_pd_TL T KD :
  NoDup (map kd_addr KD) -> incl (map kd_addr KD) (t_L (kents_T T KD)).
Proof.
  induction KD as [| d KD IH]; intros Hnd; [intros x [] |].
  inversion Hnd as [| ? ? Hn Hnd']; subst. simpl kents_T. rewrite hca5_pd_ins_eq. simpl.
  intros x [<- | Hin]; [left; reflexivity | right].
  apply hca5_pd_vremove_in; [apply IH; auto |]. intros ->. contradiction.
Qed.

Lemma hca5_pd_saddrs p KD : saddrs (map (hca5_kpool p) KD) = map kd_addr KD.
Proof. induction KD as [| d KD IH]; simpl; [reflexivity | rewrite <- IH; reflexivity]. Qed.

(* (b): the pool after kents_add *)
Lemma hca5_pd_pool p sh P T KD :
  hca5_pool p [] T -> kents_draws_ok [(p, sh, P)] KD -> itable_wf (kents_T T KD) ->
  hca5_pool p KD (kents_T T KD).
Proof.
  intros ((E & HD & He1 & He2) & _ & _) Hdr (_ & _ & Hnd & _).
  pose proof (hca5_pd_owners _ _ _ _ Hdr) as Ho.
  pose proof (hca5_pd_TD p T KD Ho) as HTD. simpl in HD. rewrite HD in HTD.
  split; [| split].
  - exists E. auto.
  - rewrite HTD in Hnd. unfold saddrs in Hnd. rewrite map_app in Hnd.
    change (map (fun '(x, _, _) => x) (map (hca5_kpool p) KD)) with (saddrs (map (hca5_kpool p) KD)) in Hnd.
    rewrite hca5_pd_saddrs in Hnd. simpl in Hnd.
    eapply Permutation_NoDup; [| exact Hnd]. symmetry. apply Permutation_cons_append.
  - apply hca5_pd_TL. destruct Hdr as [_ Hn]. exact Hn.
Qed.

(* kents_snap's precondition *)
Lemma hca5_pd_entry p T KD a :
  Forall (fun d => kd_owner d = p) KD -> In a (map kd_addr KD) ->
  In a (saddrs (t_D (kents_T T KD))) /\ e_peer (t_entry_d (kents_T T KD) a) = p.
Proof.
  intros Ho Hin. unfold t_entry_d, t_entry. rewrite (hca5_pd_TD p T KD Ho). clear Ho.
  split.
  - unfold saddrs. rewrite map_app. apply in_or_app. left.
    change (map (fun '(x, _, _) => x) (map (hca5_kpool p) KD)) with (saddrs (map (hca5_kpool p) KD)).
    rewrite hca5_pd_saddrs. exact Hin.
  - induction KD as [| d KD IH]; [destruct Hin |]. simpl.
    destruct (EqDec_val (kd_addr d) a); [reflexivity |].
    apply IH. destruct Hin as [Heq | Hin]; [congruence | exact Hin].
Qed.

Lemma hca5_pd_kents_ptr l KE : kents_rep W l KE |-- !! Forall (fun e => isptr (ke_addr e)) KE.
Proof.
  revert l; induction KE as [| e KE IH]; intros l; simpl.
  - entailer!.
  - Intros nx. unfold kent_cell. Intros. sep_apply (IH nx). Intros. apply prop_right.
    constructor; auto. exact (@field_compatible_isptr CKS _ _ _ H0).
Qed.

#[local] Instance hca5_pd_CCE : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.

Lemma hca5_pd_refs sh p r :
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p =
  @field_at W_create_any sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p.
Proof.
  assert (Hc: cs_preserve_type Noise.CS W_create_any (@coeq _ _ hca5_pd_CCE) t_peer = true)
    by (vm_compute; reflexivity).
  assert (E := @field_at_change_composite Noise.CS W_create_any hca5_pd_CCE sh t_peer
                 [StructField prot_repr3.I._refcount] (Vint r) (Vint r) (JMeq_refl _) Hc).
  exact (f_equal (fun f => f p) E).
Qed.

(* peer_rep with its reference count at the world's compspecs *)
Definition hca5_pd_prest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hca5_pd_split sh p P :
  peer_rep sh p P =
  (!! @field_compatible Noise.CS t_peer [] p &&
   (@field_at W_create_any sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
    hca5_pd_prest sh p P))%logic.
Proof.
  rewrite <- hca5_pd_refs. unfold peer_rep, hca5_pd_prest.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Lemma hca5_PD_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SB x25519 gv L FR w)
    hca5_PD
    (overridePost (hca5_SK x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_SB, hca5_SK, hca5_Delta, hca5_R. abbreviate_semax.
  Intros R S P T.
  unfold hca5_world, hca5_globs, hca5_snap0, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  unfold hca5_PD.
  assert_PROP (isptr (l_p L)) as Hpp by entailer!.
  assert (Hpn: l_p L <> nullval) by (destruct (l_p L); try contradiction; discriminate).
  replace_SEP 4 (peers_rep [(l_p L, Tsh, P)] * hnodes_rep4 W nullval []).
  { entailer!. unfold peers_rep, hnodes_rep4; simpl. entailer!. }
  forward_call (gv, Tsh, l_ita L, T, nullval, @nil hnode4, l_p L, [(l_p L, Tsh, P)], Int.one, S, w).
  { cancel. }
  { split; [apply Forall_cons; [apply writable_share_top | apply Forall_nil] |].
    split.
    - unfold kents_owners_ok. rewrite if_true by auto. split; auto. simpl. rewrite if_false; auto.
    - (* v4.1: the owners' slots are NULL or pool entries *)
      match goal with Hk: hca5_pok _ _ _ |- _ => pose proof Hk as Hpk end.
      destruct Hpk as (_ & _ & _ & _ & Hs).
      apply Forall_cons; [| apply Forall_nil].
      eapply Forall_impl; [| exact Hs]. intros v [Hv | []]. left; exact Hv. }
  Intros KD.
  match goal with Hx: kents_draws_ok _ _ |- _ => rename Hx into Hdr end.
  match goal with Hx: kents_fresh _ _ |- _ => rename Hx into Hfr end.
  pose proof (hca5_pd_owners _ _ _ _ Hdr) as Ho.
  change (negb (Int.eq Int.one Int.zero)) with true.
  rewrite (hca5_pd_PS _ _ _ _ Ho).
  change (peers_rep [(l_p L, Tsh, hca5_pd_fill P KD)]) with (peer_rep Tsh (l_p L) (hca5_pd_fill P KD) * emp).
  change (hnodes_rep4 W nullval []) with (!!(nullval = nullval) && emp).
  assert_PROP (itable_wf (kents_T T KD)) as Hwf by (unfold itable; entailer!).
  assert_PROP (Forall (fun e => isptr (ke_addr e)) (map kd_kent KD)) as Hkp
    by (sep_apply (hca5_pd_kents_ptr (kents_head KD) (map kd_kent KD)); entailer!).
  pose proof (hca5_pd_pool _ _ _ _ _ H1 Hdr Hwf) as Hpool.
  (* kents_snap(kes) *)
  forward_call (kents_head KD, map kd_kent KD, Tsh, l_ita L, kents_T T KD).
  { rewrite Forall_forall. intros e He'. apply in_map_iff in He'. destruct He' as (d & <- & Hd).
    destruct (hca5_pd_entry (l_p L) T KD (kd_addr d) Ho (in_map kd_addr _ _ Hd)) as [Hi He].
    cbn [ke_addr kd_kent]. split; [exact Hi | rewrite He; destruct (l_p L); try contradiction; discriminate]. }
  rewrite sepcon_emp. Intros.
  assert_PROP (isptr (l_wa L)) as Hwp by entailer!.
  set (P' := hca5_pd_fill P KD).
  pose proof (hca5_pd_pok L P KD H0) as Hpok'. fold P' in Hpok'.
  pose proof Hpok' as (Hd' & Hs' & Hok' & Hpk' & Hsl').
  assert (Hkp': Forall isptr (map kd_addr KD)).
  { rewrite Forall_forall in Hkp |- *. intros v Hv. apply in_map_iff in Hv. destruct Hv as (d & <- & Hd).
    apply (Hkp (kd_kent d)). apply in_map. exact Hd. }
  (* pr_take(&ps, &p) *)
  forward_call (Tsh, l_ps L, Tsh, l_p L, P').
  { rewrite Hd', Hpk'.
    assert (Hv: forall v, v = nullval \/ In v (map kd_addr KD) -> v <> Vundef).
    { intros v [-> | Hin]; [discriminate |]. rewrite Forall_forall in Hkp'. specialize (Hkp' v Hin).
      destruct v; try contradiction; discriminate. }
    rewrite Forall_forall in Hsl'.
    apply Forall_cons; [destruct (l_wa L); try contradiction; discriminate |].
    apply Forall_cons; [apply Hv, Hsl'; simpl; auto |].
    apply Forall_cons; [apply Hv, Hsl'; simpl; auto |].
    apply Forall_cons; [apply Hv, Hsl'; simpl; auto |].
    apply Forall_cons; [discriminate | apply Forall_nil]. }
  (* refs0 = p.refcount.refcount *)
  rewrite hca5_pd_split. Intros.
  forward.
  gather_SEP 1 2. replace_SEP 0 (peer_rep Tsh (l_p L) P').
  { entailer!. rewrite hca5_pd_split. entailer!. }
  (* dev_take(&ds, &wa) *)
  assert_PROP (isptr (l_pta L) /\ isptr (l_ita L)) as Hti by entailer!. destruct Hti as [Htp Hip].
  forward_call (Tsh, l_ds L, Tsh, l_wa L, hca5_D x25519 R L, Tsh, l_p L).
  { unfold hca5_D, setup_dev; cbn [d_dev d_cc cc_dev d_ptab d_itab].
    repeat (apply Forall_cons;
      [first [discriminate | match goal with |- ?v <> Vundef => destruct v; try contradiction; discriminate end] |]);
    apply Forall_nil. }
  change (d_ptab (hca5_D x25519 R L)) with (l_pta L).
  (* shim_take(&ss) *)
  forward_call (gv, Tsh, l_ss L, kents_S S KD, w).
  Exists R (kents_S S KD) P' (kents_T T KD) KD.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars, hca5_rest, hca5_kents; cbn [app].
  entailer!.
Qed.
