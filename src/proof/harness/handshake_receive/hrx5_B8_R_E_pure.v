(* law handshake_receive: phase B8, branch R: the
   segment E, its PURE part: the table facts the CHECKs of statements 10..11 need. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Local Open Scope Z_scope.

(* The final table Tf of branch R is T or t_remove T (hs_addr a) (hrx5_B8R_Tf): same pool, same membership of
   every address but hs_addr a.  PS' = supd PS a Pf (same addresses as PS).  KE' = map (kent_snapped T) KE.
   Gives: the preconditions and results of kents_same_but_next / kents_hashed / table_has / table_len on Tf,
   and the count  table_len Tf = nh (the other peers hashed in T) + [hs_addr a hashed in Tf] + kents hashed in Tf. *)
Definition hrx5_B8RE_pure_stmt : Prop :=
  forall (T Tf: tstate) (KE: list kent4) (PS PS': list (val * share * peer)) (a: val),
  t_D Tf = t_D T ->
  (forall k, k <> hs_addr a -> vin k (t_L Tf) = vin k (t_L T)) ->
  itable_wf Tf ->
  hrx5cr_pool (map ke_addr (map (kent_snapped T) KE)) PS' Tf ->
  map peer_addr4 PS' = map peer_addr4 PS ->
  NoDup (map peer_addr4 PS) ->
  Forall (fun x => isptr (peer_addr4 x)) PS ->
  In a (map peer_addr4 PS) ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D Tf)) /\ ke_snap e <> None /\
           Forall (vp_ok (saddrs (t_D Tf) ++ vobjs_addrs [VPeers PS'])) (kent_ptrs_nn Tf e))
    (map (kent_snapped T) KE) /\
  forallb (kent_same_bn Tf) (map (kent_snapped T) KE) = true /\
  Forall (fun e => In (ke_addr e) (saddrs (t_D Tf))) (map (kent_snapped T) KE) /\
  In (hs_addr a) (saddrs (t_D Tf)) /\
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) (t_D Tf) /\
  Zlength (t_L Tf) =
    hrx5_B8R_nh T a PS + (if vin (hs_addr a) (t_L Tf) then 1 else 0) +
    kents_hashed_n Tf (map (kent_snapped T) KE).

Ltac hrx5_B8RE_dif := match goal with |- context [if ?c then _ else _] => destruct c end.

(* ---- reflexivity of the comparisons (port of hcl5_P8) ---- *)
Lemma hrx5_B8RE_veqb_refl x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.
Lemma hrx5_B8RE_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.
Lemma hrx5_B8RE_entry_eqb_refl E : entry_eqb E E = true.
Proof. unfold entry_eqb. hrx5_B8RE_dif; [|congruence]. rewrite !Int.eq_true. reflexivity. Qed.
Lemma hrx5_B8RE_int64s_eqb_refl l : int64s_eqb l l = true.
Proof. induction l; cbn; auto. rewrite Int64.eq_true; auto. Qed.
Lemma hrx5_B8RE_kp_eqb_refl K : kp_eqb K K = true.
Proof.
  unfold kp_eqb, symkey_eqb. rewrite !hrx5_B8RE_bytes_eqb_refl, !Int64.eq_true, !Int.eq_true, !Bool.eqb_reflx,
    hrx5_B8RE_int64s_eqb_refl. reflexivity.
Qed.

Lemma hrx5_B8RE_nodup_app_r (l1 l2: list val) x : NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  induction l1 as [|y l1 IH]; cbn; intros Hn Hx Hin; [auto|]. inversion Hn; subst.
  destruct Hin as [<- | Hin]; [apply H1; apply in_or_app; right; auto | eapply IH; eauto].
Qed.

(* ---- counting ---- *)
Lemma hrx5_B8RE_count (L U: list val) : NoDup L -> NoDup U -> incl L U ->
  Zlength L = Zlength (filter (fun x => vin x L) U).
Proof.
  intros HL HU HI. rewrite !Zlength_correct. f_equal. apply Nat.le_antisymm; apply NoDup_incl_length.
  - exact HL.
  - intros x Hx. apply filter_In. split; [apply HI, Hx|].
    unfold vin. destruct (in_dec eq_dec x L); [reflexivity | contradiction].
  - apply NoDup_filter, HU.
  - intros x Hx. apply filter_In in Hx. destruct Hx as [Hx Hv].
    unfold vin in Hv. destruct (in_dec eq_dec x L); [auto | discriminate].
Qed.

Lemma hrx5_B8RE_filter_map {A B: Type} (g: B -> bool) (f: A -> B) l :
  Zlength (filter g (map f l)) = Zlength (filter (fun x => g (f x)) l).
Proof. induction l as [|x l IH]; cbn; auto. destruct (g (f x)); rewrite ?Zlength_cons, IH; auto. Qed.

Lemma hrx5_B8RE_hs_veqb y p : isptr y -> isptr p -> veqb (hs_addr y) (hs_addr p) = veqb y p.
Proof.
  intros Hy Hp. destruct y; try contradiction. destruct p; try contradiction.
  unfold veqb, hs_addr.
  match goal with |- (if ?c then _ else _) = (if ?d then _ else _) => destruct c as [E'|E']; destruct d as [E|E] end;
    auto; exfalso.
  - apply E. cbn in E'. assert (Hb: b = b0) by congruence. subst b0. f_equal.
    assert (Hq: Ptrofs.add i (Ptrofs.repr OFS_PEER_HANDSHAKE) = Ptrofs.add i0 (Ptrofs.repr OFS_PEER_HANDSHAKE))
      by congruence.
    match goal with Hq: Ptrofs.add ?x ?r = Ptrofs.add ?y ?r |- _ =>
      apply (f_equal (fun z => Ptrofs.sub z r)) in Hq; rewrite !Ptrofs.sub_add_opp, !Ptrofs.add_assoc,
        !Ptrofs.add_neg_zero, !Ptrofs.add_zero in Hq; exact Hq end.
  - apply E'. rewrite E. reflexivity.
Qed.

Lemma hrx5_B8RE_hs_inj y p : isptr y -> isptr p -> hs_addr y = hs_addr p -> y = p.
Proof.
  intros Hy Hp E. pose proof (hrx5_B8RE_hs_veqb y p Hy Hp) as X. rewrite E, hrx5_B8RE_veqb_refl in X.
  unfold veqb in X. destruct (eq_dec y p); [auto | discriminate].
Qed.

(* the peers' part of the count *)
Lemma hrx5_B8RE_cnt0 (l: list val) a Lf LT :
  (forall k, k <> hs_addr a -> vin k Lf = vin k LT) ->
  Forall isptr l -> isptr a -> ~ In a l ->
  Zlength (filter (fun y => vin (hs_addr y) Lf) l) =
  Zlength (filter (fun y => andb (negb (veqb y a)) (vin (hs_addr y) LT)) l).
Proof.
  intros Hv Hp Ha Hn. f_equal. apply filter_ext_in. intros y Hy.
  rewrite Forall_forall in Hp. unfold veqb. destruct (eq_dec y a) as [<-|Hne]; [contradiction|].
  cbn [negb andb]. apply Hv. intros X. apply Hne. apply hrx5_B8RE_hs_inj; auto.
Qed.

Lemma hrx5_B8RE_cnt (l: list val) a Lf LT :
  (forall k, k <> hs_addr a -> vin k Lf = vin k LT) ->
  NoDup l -> Forall isptr l -> isptr a -> In a l ->
  Zlength (filter (fun y => vin (hs_addr y) Lf) l) =
  Zlength (filter (fun y => andb (negb (veqb y a)) (vin (hs_addr y) LT)) l) + (if vin (hs_addr a) Lf then 1 else 0).
Proof.
  intros Hv. induction l as [|y l IH]; intros Hn Hp Ha Hin; [contradiction|].
  inversion Hn as [|? ? Hy Hn']; subst. inversion Hp as [|? ? Hpy Hp']; subst.
  cbn [filter]. unfold veqb at 1. destruct (eq_dec y a) as [<-|Hne].
  - cbn [negb andb]. pose proof (hrx5_B8RE_cnt0 l y Lf LT Hv Hp' Ha Hy) as X.
    destruct (vin (hs_addr y) Lf); rewrite ?Zlength_cons; lia.
  - cbn [negb andb]. destruct Hin as [X|Hin]; [congruence|].
    rewrite Hv by (intros X; apply Hne; apply hrx5_B8RE_hs_inj; auto).
    destruct (vin (hs_addr y) LT); rewrite ?Zlength_cons, IH by auto; lia.
Qed.

(* ---- the pool ---- *)
Lemma hrx5_B8RE_saddrs_app (l1 l2: list (val * share * entry)) : saddrs (l1 ++ l2) = saddrs l1 ++ saddrs l2.
Proof. unfold saddrs. apply map_app. Qed.

Lemma hrx5_B8RE_F2_ke PS KA (L: list (val * share * entry)) : Forall2 (hrx5cr_ke_ok PS) KA L ->
  saddrs L = KA /\ Forall (fun x => match x with (_, sh, _) => sh = Ews end) L /\
  (forall k, In k KA -> exists sh E, In (k, sh, E) L /\ In (e_peer E) (map peer_addr4 PS)).
Proof.
  induction 1 as [|k [[a sh] E] KA L Hk _ (IH1 & IH2 & IH3)].
  - split; [reflexivity|]. split; [constructor|]. intros k [].
  - destruct Hk as (-> & -> & Hp & _). split; [|split].
    + change (saddrs ((k, Ews, E) :: L)) with (k :: saddrs L). rewrite IH1; reflexivity.
    + constructor; auto.
    + intros k' [<- | Hk'].
      * exists Ews, E. split; [left; reflexivity | exact Hp].
      * destruct (IH3 k' Hk') as (sh' & E' & H1 & H2). exists sh', E'. split; [right; exact H1 | exact H2].
Qed.

Lemma hrx5_B8RE_F2_hs PS (L: list (val * share * entry)) : Forall2 hrx5cr_hs_ok PS L ->
  saddrs L = map (fun x => hs_addr (peer_addr4 x)) PS /\
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) L.
Proof.
  induction 1 as [|[[p sp] P] [[a sh] E] PS L Hk _ [IH1 IH2]].
  - split; [reflexivity | constructor].
  - destruct Hk as (-> & -> & _ & _). split.
    + change (saddrs ((hs_addr p, Ews, E) :: L)) with (hs_addr p :: saddrs L). rewrite IH1; reflexivity.
    + constructor; auto.
Qed.

Lemma hrx5_B8RE_pool KA PS T : hrx5cr_pool KA PS T ->
  saddrs (t_D T) = KA ++ map (fun x => hs_addr (peer_addr4 x)) PS /\
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) (t_D T) /\
  (forall k, In k KA -> exists sh E, In (k, sh, E) (t_D T) /\ In (e_peer E) (map peer_addr4 PS)).
Proof.
  intros [H1 H2]. apply hrx5_B8RE_F2_ke in H1 as (A1 & B1 & C1). apply hrx5_B8RE_F2_hs in H2 as [A2 B2].
  rewrite <- (firstn_skipn (length KA) (t_D T)). split; [|split].
  - rewrite hrx5_B8RE_saddrs_app, A1, A2. reflexivity.
  - apply Forall_app; auto.
  - intros k Hk. destruct (C1 k Hk) as (sh & E & X & Y). exists sh, E. split; [apply in_or_app; left; exact X | exact Y].
Qed.

Lemma hrx5_B8RE_sfind (D: list (val * share * entry)) k sh E : NoDup (saddrs D) -> In (k, sh, E) D ->
  sfind D k = Some (sh, E).
Proof.
  induction D as [|[[x s] F] D IH]; intros Hn Hin; [contradiction|].
  change (saddrs ((x, s, F) :: D)) with (x :: saddrs D) in Hn.
  inversion Hn as [|? ? Hx Hn']; subst. cbn [sfind].
  destruct Hin as [Heq | Hin].
  - inversion Heq; subst. destruct (eq_dec k k); congruence.
  - destruct (eq_dec x k) as [<-|Hne]; [|auto]. exfalso. apply Hx. unfold saddrs. apply in_map_iff.
    exists (x, sh, E); auto.
Qed.

Lemma hrx5_B8RE_pure : hrx5_B8RE_pure_stmt.
Proof.
  intros T Tf KE PS PS' a HD Hv Hwf Hpool HPS HnP HpP Ha.
  destruct (hrx5_B8RE_pool _ _ _ Hpool) as (HS0 & HEws & HK).
  set (KE' := map (kent_snapped T) KE) in *. set (KA := map ke_addr KE') in *.
  assert (HS: saddrs (t_D Tf) = KA ++ map hs_addr (map peer_addr4 PS)).
  { rewrite HS0, <- HPS, map_map. reflexivity. }
  destruct Hwf as (HnL & Hincl & HnD & _).
  assert (Hha: In (hs_addr a) (map hs_addr (map peer_addr4 PS))) by (apply in_map, Ha).
  assert (HnK: ~ In (hs_addr a) KA) by (rewrite HS in HnD; eapply hrx5_B8RE_nodup_app_r; eauto).
  assert (HE: forall k, t_entry_d Tf k = t_entry_d T k) by (intros; unfold t_entry_d, t_entry; rewrite HD; reflexivity).
  assert (HKA: forall e, In e KE -> In (ke_addr e) KA).
  { intros e He. unfold KA, KE'. rewrite map_map. change (ke_addr e) with ((fun x => ke_addr (kent_snapped T x)) e).
    apply in_map, He. }
  assert (Hkin: Forall (fun e => In (ke_addr e) (saddrs (t_D Tf))) KE').
  { unfold KE'. apply Forall_map, Forall_forall. intros e He. change (ke_addr (kent_snapped T e)) with (ke_addr e).
    rewrite HS. apply in_or_app; left; exact (HKA e He). }
  split; [|split; [|split; [exact Hkin|split; [|split]]]].
  - unfold KE'. apply Forall_map, Forall_forall. intros e He.
    unfold Basics.compose, kent_snapped, kent_ptrs_nn. cbn [ke_addr ke_snap ks_E].
    destruct (HK (ke_addr e) (HKA e He)) as (sh & E & H1 & H2).
    assert (Hent: t_entry_d T (ke_addr e) = E).
    { unfold t_entry_d, t_entry. rewrite <- HD, (hrx5_B8RE_sfind _ _ sh E HnD H1). reflexivity. }
    rewrite HE, Hent.
    assert (Hvp: vp_ok (saddrs (t_D Tf) ++ vobjs_addrs [VPeers PS']) (e_peer E)).
    { right. apply in_or_app. right. unfold vobjs_addrs. cbn. rewrite app_nil_r. exact H2. }
    split; [rewrite HS; apply in_or_app; left; exact (HKA e He)|].
    split; [discriminate|]. constructor; [exact Hvp | constructor; [exact Hvp | constructor]].
  - apply forallb_forall. intros e' Hin. unfold KE' in Hin. apply in_map_iff in Hin. destruct Hin as (e & <- & He).
    assert (Hne: ke_addr e <> hs_addr a) by (intros X; apply HnK; rewrite <- X; apply HKA, He).
    unfold kent_same_bn, kent_eqb_cur, kent_snapped, kent_eqb_nn. cbn [ke_snap ke_addr ke_K ks_E ks_hashed ks_K].
    rewrite HE, Hv by exact Hne.
    rewrite hrx5_B8RE_entry_eqb_refl, Bool.eqb_reflx, hrx5_B8RE_kp_eqb_refl.
    destruct (vin _ _); reflexivity.
  - rewrite HS. apply in_or_app; right; exact Hha.
  - exact HEws.
  - rewrite (hrx5_B8RE_count (t_L Tf) (saddrs (t_D Tf))) by auto.
    rewrite HS, filter_app, Zlength_app, !hrx5_B8RE_filter_map.
    unfold KA, kents_hashed_n. rewrite hrx5_B8RE_filter_map.
    assert (Hpa: Forall isptr (map peer_addr4 PS)) by (apply Forall_map; exact HpP).
    assert (Hap: isptr a) by (rewrite Forall_forall in Hpa; apply Hpa, Ha).
    pose proof (hrx5_B8RE_cnt (map peer_addr4 PS) a (t_L Tf) (t_L T) Hv HnP Hpa Hap Ha) as X.
    rewrite !hrx5_B8RE_filter_map in X. unfold hrx5_B8R_nh. lia.
Qed.
