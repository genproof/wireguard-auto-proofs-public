(* law create_any, phase PH: the pure facts of segment H about the
   current table T' (the snapshot table T, or T with p's handshake entry reinserted): the pool keeps its shape, the
   kents' entries and membership are unchanged, the length of the table's list, and kents_same_but_next's
   precondition and result. (hca3_PH_len, hca3_PH_pool_k) and
   (hca3_PG_pool_ins). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
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

(* ---- pure facts on the pool (ports of v1 hca3_PG / hca3_PH) ---- *)

Lemma hca5_PH_pure_vremove_in a x L : In x L -> x <> a -> In x (vremove a L).
Proof.
  induction L as [|y L IH]; simpl; intros H N; [contradiction|].
  destruct (EqDec_val y a); [subst; destruct H; [congruence|auto]|].
  destruct H; [left; auto | right; auto].
Qed.

Lemma hca5_PH_pure_psfind (p: val) (KD: list kdraw) (E: entry) :
  ~ In (hs_addr p) (map kd_addr KD) ->
  sfind (map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E)]) (hs_addr p) = Some (Tsh, E).
Proof.
  induction KD as [|K KD IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intros e; apply Hn; auto).
    apply IH. intros Hi; apply Hn; auto.
Qed.

Lemma hca5_PH_pure_psupd (p: val) (KD: list kdraw) (E E': entry) :
  ~ In (hs_addr p) (map kd_addr KD) ->
  supd (map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E)]) (hs_addr p) E' =
  map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E')].
Proof.
  induction KD as [|K KD IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intros e; apply Hn; auto).
    f_equal. apply IH. intros Hi; apply Hn; auto.
Qed.

Lemma hca5_PH_pure_ksfind (p: val) (KD: list kdraw) (E: entry) (K: kdraw) :
  NoDup (map kd_addr KD) -> In K KD ->
  sfind (map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E)]) (kd_addr K) =
  Some (Ews, mkEntry p IDX_KEYPAIR (kd_idx K)).
Proof.
  induction KD as [|K0 KD IH]; intros Hnd Hin; [contradiction |].
  simpl in Hnd |- *. inversion Hnd as [| x l Hx Hnd']; subst.
  destruct Hin as [<- | Hin].
  - rewrite if_true by auto. reflexivity.
  - rewrite if_false. { apply IH; auto. }
    intros Heq. apply Hx. rewrite Heq. apply in_map; auto.
Qed.

Lemma hca5_PH_pure_pool_ins p KD T idx :
  hca5_pool p KD T -> hca5_pool p KD (t_insert T (hs_addr p) idx).
Proof.
  intros HP. pose proof HP as [[E [HD [Hp Ht]]] [Hnd Hinc]].
  pose proof Hnd as Hnd0. apply NoDup_cons_iff in Hnd0 as [Hx _].
  assert (HS: t_entry T (hs_addr p) = Some E).
  { unfold t_entry. rewrite HD. rewrite hca5_PH_pure_psfind by assumption. reflexivity. }
  unfold hca5_pool, t_insert, t_set_index. rewrite HS. unfold t_upd. cbn [t_D t_L].
  split; [|split; [exact Hnd|]].
  - exists (mkEntry (e_peer E) (e_type E) idx). rewrite HD.
    rewrite hca5_PH_pure_psupd by assumption. auto.
  - intros y Hy. right. apply hca5_PH_pure_vremove_in; auto.
    intros ->. auto.
Qed.

Lemma hca5_PH_pure_pool_k p KD T K :
  hca5_pool p KD T -> In K KD ->
  sfind (t_D T) (kd_addr K) = Some (Ews, mkEntry p IDX_KEYPAIR (kd_idx K)) /\
  vin (kd_addr K) (t_L T) = true.
Proof.
  intros [[E [HD _]] [Hnd Hinc]] Hin. apply NoDup_cons_iff in Hnd as [_ Hnd]. split.
  - rewrite HD. apply hca5_PH_pure_ksfind; auto.
  - unfold vin. destruct (in_dec _ _ _) as [_ | N]; [auto |].
    exfalso. apply N, Hinc, in_map; auto.
Qed.

Lemma hca5_PH_pure_saddrs p KD E :
  saddrs (map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E)]) = map kd_addr KD ++ [hs_addr p].
Proof. unfold saddrs. rewrite map_app, map_map. reflexivity. Qed.

Lemma hca5_PH_pure_len p KD T :
  hca5_pool p KD T -> itable_wf T ->
  Zlength (t_L T) = Zlength KD + (if vin (hs_addr p) (t_L T) then 1 else 0).
Proof.
  intros [[E [HD _]] [Hnd Hinc]] (HndL & HincL & _).
  rewrite HD, hca5_PH_pure_saddrs in HincL.
  apply NoDup_cons_iff in Hnd as [Hx Hnd'].
  set (A := map kd_addr KD ++ (if vin (hs_addr p) (t_L T) then [hs_addr p] else [])).
  assert (HndA: NoDup A).
  { unfold A. apply NoDup_app_iff. split; [auto | split].
    - destruct (vin _ _); repeat constructor; auto.
    - intros y Hy Hy'. destruct (vin _ _); [| contradiction].
      destruct Hy' as [<- | []]. contradiction. }
  assert (H1: incl A (t_L T)).
  { unfold A. intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy | Hy]; [auto |].
    unfold vin in Hy. destruct (in_dec _ _ _); [| contradiction].
    destruct Hy as [<- | []]; auto. }
  assert (H2: incl (t_L T) A).
  { intros y Hy. pose proof (HincL y Hy) as Hy'. apply in_app_or in Hy'. unfold A.
    apply in_or_app. destruct Hy' as [Hy' | [<- | []]]; [left; auto | right].
    unfold vin. destruct (in_dec _ _ _); [left; auto | contradiction]. }
  pose proof (NoDup_incl_length HndA H1). pose proof (NoDup_incl_length HndL H2).
  assert (Zlength (t_L T) = Zlength A).
  { rewrite !Zlength_correct. f_equal. lia. }
  rewrite H3. unfold A. rewrite Zlength_app, Zlength_map.
  destruct (vin _ _); reflexivity.
Qed.

Lemma hca5_PH_pure_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hca5_PH_pure_int64s_eqb_refl a : int64s_eqb a a = true.
Proof. induction a; simpl; auto. rewrite Int64.eq_true; auto. Qed.

Lemma hca5_PH_pure_kp_eqb_refl K : kp_eqb K K = true.
Proof.
  unfold kp_eqb, symkey_eqb.
  rewrite !Int.eq_true, !Int64.eq_true, !hca5_PH_pure_bytes_eqb_refl, !Bool.eqb_reflx,
    hca5_PH_pure_int64s_eqb_refl. reflexivity.
Qed.

Lemma hca5_PH_pure_entry_eqb_refl E : entry_eqb E E = true.
Proof.
  unfold entry_eqb. rewrite if_true by auto. rewrite !Int.eq_true. reflexivity.
Qed.

(* everything segment H needs to know about the table T' *)
Lemma hca5_PH_facts (p: val) (KD: list kdraw) (T T': tstate) (sh: share) (P': peer) :
  hca5_pool p KD T -> itable_wf T' ->
  (T' = T \/ (exists idx, T' = t_insert T (hs_addr p) idx)) ->
  (exists E, sfind (t_D T') (hs_addr p) = Some (Tsh, E) /\ e_peer E = p /\ e_type E = IDX_HANDSHAKE) /\
  (forall d, In d KD ->
     sfind (t_D T') (kd_addr d) = Some (Ews, mkEntry p IDX_KEYPAIR (kd_idx d)) /\
     vin (kd_addr d) (t_L T') = true) /\
  Zlength (t_L T') = Zlength KD + (if vin (hs_addr p) (t_L T') then 1 else 0) /\
  Forall (fun e => In (ke_addr e) (saddrs (t_D T')) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D T') ++ vobjs_addrs [VPeer sh p P'])) (kent_ptrs_nn T' e))
    (hca5_kents T KD) /\
  forallb (kent_same_bn T') (hca5_kents T KD) = true.
Proof.
  intros HP WF HT'.
  assert (HP': hca5_pool p KD T').
  { destruct HT' as [-> | [idx ->]]; [exact HP | apply (hca5_PH_pure_pool_ins p KD T idx HP)]. }
  assert (HK: forall d, In d KD ->
     sfind (t_D T') (kd_addr d) = Some (Ews, mkEntry p IDX_KEYPAIR (kd_idx d)) /\
     vin (kd_addr d) (t_L T') = true) by (intros d Hd; eapply hca5_PH_pure_pool_k; eauto).
  assert (HK0: forall d, In d KD ->
     sfind (t_D T) (kd_addr d) = Some (Ews, mkEntry p IDX_KEYPAIR (kd_idx d)) /\
     vin (kd_addr d) (t_L T) = true) by (intros d Hd; eapply hca5_PH_pure_pool_k; eauto).
  pose proof HP' as [[E' [HD' [Hp' Ht']]] [Hnd' _]].
  split; [| split; [exact HK | split; [apply hca5_PH_pure_len; auto | split]]].
  - exists E'. rewrite HD'. apply NoDup_cons_iff in Hnd' as [Hx _].
    rewrite hca5_PH_pure_psfind by assumption. auto.
  - unfold hca5_kents. rewrite map_map. apply Forall_map. apply Forall_forall. intros d Hd.
    destruct (HK d Hd) as [S1 V1]. destruct (HK0 d Hd) as [S0 V0].
    unfold Basics.compose. cbv beta.
    unfold kent_snapped, kd_kent, kent_ptrs_nn, t_entry_d, t_entry; cbn [ke_addr ke_snap ke_K ks_E].
    rewrite S0, S1. cbn [e_peer]. split; [| split; [discriminate |]].
    + rewrite HD', hca5_PH_pure_saddrs. apply in_or_app; left. apply in_map; auto.
    + cbn [vobjs_addrs map vobj_addrs concat]. 
      apply Forall_forall; intros x Hx; right; destruct Hx as [<-|[<-|[]]]; apply in_or_app; right; simpl; auto.
  - unfold hca5_kents. rewrite map_map. apply forallb_forall. intros e He.
    apply in_map_iff in He as [d [<- Hd]].
    destruct (HK d Hd) as [S1 V1]. destruct (HK0 d Hd) as [S0 V0].
    unfold kent_same_bn, kent_eqb_cur, kent_eqb_nn, kent_snapped, kd_kent, t_entry_d, t_entry;
      cbn [ke_addr ke_snap ke_K ks_E ks_hashed ks_K].
    rewrite S0, S1, V0, V1, hca5_PH_pure_entry_eqb_refl, hca5_PH_pure_kp_eqb_refl. reflexivity.
Qed.
