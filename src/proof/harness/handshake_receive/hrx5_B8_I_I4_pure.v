(* law handshake_receive, phase B8 branch I, segment I4:
   copy (stems hrx5_b8i4_) of branch C's hrx5_B8_C_W_pure.v: the pure facts of CHECK(hnodes_same_except(peers, target->p) && itd.head == head0 && kents_same(kes) && shim_same(&ss)).
   Port of consume_response_any's hcr5_q5_pure.v (the hq5_ lemmas) and consume_initiation_any's hci5_p8_b_pure.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Local Open Scope Z_scope.

Ltac hrx5_b8i4_dif := match goal with |- context [if ?d then _ else _] => destruct d end.

(* the snapshots of the nodes *)
Definition hrx5_b8i4_sns (T: tstate) (PS: list (val * share * peer)) : list hsnap :=
  map (fun x => match x with (p, _, P) => hs_snap_cur T p P end) PS.
Definition hrx5_b8i4_rs (PS: list (val * share * peer)) : list int :=
  map (fun x => match x with (_, _, P) => p_refs P end) PS.
Definition hrx5_b8i4_prs (PS: list (val * share * peer)) : list peer :=
  map (fun x => match x with (_, _, P) => P end) PS.

(* ---- reflexivity of the comparisons ---- *)
Lemma hrx5_b8i4_veqb x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hrx5_b8i4_bytes A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

Lemma hrx5_b8i4_snap_eqb_refl: forall s, snap_eqb s s = true.
Proof.
  intros [[p ty ix] nx hb H]. unfold snap_eqb, entry_eqb, hs_eqb, bytes_eqb; simpl.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hrx5_b8i4_pr_eqb_refl: forall P, pr_eqb P P = true.
Proof.
  intros P. unfold pr_eqb, pr_eqb_nc, cookie_eqb, veqb, bytes_eqb.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hrx5_b8i4_shim_refl S w : shim_eqb S w S w = true.
Proof. unfold shim_eqb, warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity. Qed.

Lemma hrx5_b8i4_int64s l : int64s_eqb l l = true.
Proof. induction l as [| x l IH]; cbn; [reflexivity | rewrite Int64.eq_true, IH; reflexivity]. Qed.

Lemma hrx5_b8i4_symkey A : symkey_eqb A A = true.
Proof. unfold symkey_eqb. rewrite hrx5_b8i4_bytes, Int64.eq_true, Bool.eqb_reflx. reflexivity. Qed.

Lemma hrx5_b8i4_kp K : kp_eqb K K = true.
Proof.
  unfold kp_eqb. rewrite !hrx5_b8i4_symkey, !Int64.eq_true, !Int.eq_true, Bool.eqb_reflx, hrx5_b8i4_int64s.
  reflexivity.
Qed.

Lemma hrx5_b8i4_entry E : entry_eqb E E = true.
Proof. unfold entry_eqb. destruct (eq_dec (e_peer E) (e_peer E)); [| congruence]. rewrite !Int.eq_true. reflexivity. Qed.

Lemma hrx5_b8i4_kents_refl T KE : forallb (kent_same T) (map (kent_snapped T) KE) = true.
Proof.
  induction KE as [| e KE IH]; [reflexivity |]. cbn [map forallb]. rewrite IH, andb_true_r.
  unfold kent_same, kent_snapped, kent_eqb_cur, kent_eqb_nn; cbn.
  rewrite hrx5_b8i4_entry, Bool.eqb_reflx, hrx5_b8i4_kp, hrx5_b8i4_veqb. reflexivity.
Qed.

Lemma hrx5_b8i4_khead_snapped T KE : hrx5_khead (map (kent_snapped T) KE) = hrx5_khead KE.
Proof. destruct KE; reflexivity. Qed.

(* ---- lists ---- *)
Lemma hrx5_b8i4_sfind_nodup: forall (l: list (val * share * entry)) a sh v,
  NoDup (saddrs l) -> In (a, sh, v) l -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros a sh v Hn H; [contradiction|].
  unfold saddrs in Hn; simpl in Hn; inv Hn.
  destruct (eq_dec x a) as [->|n]; [rewrite if_true by auto|rewrite if_false by auto].
  - destruct H as [H|H]; [inv H; reflexivity|].
    exfalso; apply H2. apply (in_map (fun '(x, _, _) => x) l (a, sh, v)) in H; exact H.
  - destruct H as [H|H]; [inv H; congruence|]. apply IH; auto.
Qed.

Lemma hrx5_b8i4_hs_in: forall D PS l, Forall2 hrx5cr_hs_ok PS l -> incl l D ->
  Forall (fun x => exists E, In (hs_addr (peer_addr4 x), Ews, E) D /\ e_peer E = peer_addr4 x /\
                            e_type E = IDX_HANDSHAKE) PS.
Proof.
  intros D PS l H; induction H as [|y x PS0 l0 Hyx HF IH]; intros Hi; constructor.
  - destruct y as [[p sh] P], x as [[a s] E]; simpl in Hyx. destruct Hyx as (-> & -> & HE & Ht).
    exists E. simpl. split; [apply Hi; left; reflexivity | auto].
  - apply IH. intros z Hz; apply Hi; right; auto.
Qed.

Lemma hrx5_b8i4_pool_in: forall KA PS T, hrx5cr_pool KA PS T ->
  Forall (fun x => exists E, In (hs_addr (peer_addr4 x), Ews, E) (t_D T) /\ e_peer E = peer_addr4 x /\
                            e_type E = IDX_HANDSHAKE) PS.
Proof.
  intros KA PS T (_ & H). eapply hrx5_b8i4_hs_in; [exact H|].
  intros y Hy. rewrite <- (firstn_skipn (length KA) (t_D T)). apply in_or_app; right; auto.
Qed.

Lemma hrx5_b8i4_pool_entry_wf: forall KA PS T, hrx5cr_pool KA PS T -> itable_wf T ->
  Forall (fun x => In (hs_addr (peer_addr4 x)) (saddrs (t_D T)) /\
                   exists E, t_entry T (hs_addr (peer_addr4 x)) = Some E /\ e_peer E = peer_addr4 x /\
                            e_type E = IDX_HANDSHAKE) PS.
Proof.
  intros KA PS T Hp (_ & _ & Hn & _). eapply Forall_impl; [|apply (hrx5_b8i4_pool_in _ _ _ Hp)].
  intros x (E & HI & H1 & H2). split.
  - apply (in_map (fun '(x, _, _) => x) (t_D T) _) in HI; exact HI.
  - exists E. unfold t_entry. rewrite (hrx5_b8i4_sfind_nodup _ _ _ _ Hn HI). auto.
Qed.

Lemma hrx5_b8i4_F2_in {A B: Type} (Rl: A -> B -> Prop) (l1: list A) (l2: list B) k :
  Forall2 Rl l1 l2 -> In k l1 -> exists x, In x l2 /\ Rl k x.
Proof.
  intros H; induction H as [|k0 x l1 l2 Hkx HF IH]; intros Hin; [contradiction|].
  destruct Hin as [<-|Hin]; [exists x; split; [left; reflexivity | exact Hkx]|].
  destruct (IH Hin) as (y & Hy & Hky). exists y. split; [right; exact Hy | exact Hky].
Qed.

(* the kents' entries: in the pool, of a peer of PS *)
Lemma hrx5_b8i4_pool_ke: forall KE PS T, hrx5cr_pool (map ke_addr KE) PS T -> itable_wf T ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ In (e_peer (t_entry_d T (ke_addr e))) (map peer_addr4 PS)) KE.
Proof.
  intros KE PS T (H1 & _) (_ & _ & Hn & _).
  apply Forall_forall. intros e He.
  assert (Hk: exists x, In x (firstn (length (map ke_addr KE)) (t_D T)) /\ hrx5cr_ke_ok PS (ke_addr e) x).
  { apply (in_map ke_addr) in He. exact (hrx5_b8i4_F2_in _ _ _ _ H1 He). }
  destruct Hk as ([[a sh] E] & Hin & (Ha & Hsh & Hp & _)). subst a sh.
  assert (HinD: In (ke_addr e, Ews, E) (t_D T)).
  { rewrite <- (firstn_skipn (length (map ke_addr KE)) (t_D T)). apply in_or_app; left; exact Hin. }
  split.
  - apply (in_map (fun '(x, _, _) => x) (t_D T) _) in HinD; exact HinD.
  - unfold t_entry_d, t_entry. rewrite (hrx5_b8i4_sfind_nodup _ _ _ _ Hn HinD).
    replace (map peer_addr4 PS) with (map hrx5cr_paddr PS); [exact Hp|].
    apply map_ext. intros [[x s] P]; reflexivity.
Qed.

Lemma hrx5_b8i4_snapped_cons: forall T N NS x PS,
  hnodes_snapped4 T (N :: NS) (x :: PS) = hn_snapshot4 T N x :: hnodes_snapped4 T NS PS.
Proof. reflexivity. Qed.

Lemma hrx5_b8i4_snapped_p: forall T NS PS, length NS = length PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hl; try discriminate; [reflexivity|].
  rewrite hrx5_b8i4_snapped_cons. simpl. rewrite IH by auto. destruct x as [[p sh] P]; reflexivity.
Qed.

Lemma hrx5_b8i4_peers_len: forall NS PS, hnodes_peers4 NS PS -> length NS = length PS.
Proof.
  intros NS PS H. unfold hnodes_peers4 in H.
  rewrite <- (map_length hn_p NS), H, map_length. reflexivity.
Qed.

Lemma hrx5_b8i4_snapped_vals: forall T NS PS, length NS = length PS ->
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hrx5_b8i4_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hrx5_b8i4_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hrx5_b8i4_prs PS) /\
  length (hnodes_snapped4 T NS PS) = length PS.
Proof.
  induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hl; try discriminate; [auto|].
  destruct (IH PS) as (H1 & H2 & H3 & H4); [simpl in Hl; lia|].
  rewrite hrx5_b8i4_snapped_cons. destruct x as [[p sh] P].
  unfold hrx5_b8i4_sns, hrx5_b8i4_rs, hrx5_b8i4_prs in *.
  cbn [map length]. rewrite H1, H2, H3, H4. auto.
Qed.

Lemma hrx5_b8i4_supd_addr: forall (PS: list (val * share * peer)) a P',
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [|[[x s] w] PS IH]; simpl; intros; auto.
  hrx5_b8i4_dif; simpl; f_equal; auto.
Qed.

Lemma hrx5_b8i4_supd_wf: forall PS a P', peers_wf PS -> peers_wf (supd PS a P').
Proof.
  unfold peers_wf. induction PS as [|[[x s] w] PS IH]; simpl; intros a P' H; auto.
  inv H. hrx5_b8i4_dif; constructor; auto.
Qed.

Lemma hrx5_b8i4_succ_in: forall L a, succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; intros a; auto.
  hrx5_b8i4_dif.
  - destruct L; simpl; auto.
  - destruct (IH a); auto.
Qed.

Lemma hrx5_b8i4_vp_mono: forall own own' x, incl own own' -> vp_ok own x -> vp_ok own' x.
Proof. intros own own' x Hi [H|H]; [left; auto | right; auto]. Qed.

Lemma hrx5_b8i4_chain_head: forall head PS, pk_chain head PS -> vp_ok (map peer_addr4 PS) head.
Proof.
  intros head [|[[a s] P] PS]; simpl; intros H; [left; auto | right; left; symmetry; apply H].
Qed.

Lemma hrx5_b8i4_chain_next: forall head PS, pk_chain head PS ->
  Forall (fun x => match x with (_, _, P) => vp_ok (map peer_addr4 PS) (p_pknext P) end) PS.
Proof.
  intros head PS; revert head; induction PS as [|[[a s] P] PS IH]; intros head H; constructor.
  - destruct H as [_ H]. eapply hrx5_b8i4_vp_mono; [|apply (hrx5_b8i4_chain_head _ _ H)].
    intros y Hy; right; auto.
  - destruct H as [_ H]. eapply Forall_impl; [|apply (IH _ H)].
    intros [[b t] Q] Hb. eapply hrx5_b8i4_vp_mono; [|exact Hb]. intros y Hy; right; auto.
Qed.

(* the relation between PS and PS' (one peer updated keeping its pointers) *)
Definition hrx5_b8i4_R (x x': val * share * peer) : Prop :=
  match x, x' with (p, _, P), (p', _, P') =>
    p' = p /\ hs_sid (p_hs P') = hs_sid (p_hs P) /\ pr_ptrs P P' = pr_ptrs P P end.

Lemma hrx5_b8i4_R_refl: forall PS, Forall2 hrx5_b8i4_R PS PS.
Proof. induction PS as [|[[p s] P] PS IH]; constructor; simpl; auto. Qed.

Lemma hrx5_b8i4_R_supd: forall PS a P',
  (forall sh P0, sfind PS a = Some (sh, P0) -> hs_sid (p_hs P') = hs_sid (p_hs P0) /\ pr_ptrs P0 P' = pr_ptrs P0 P0) ->
  Forall2 hrx5_b8i4_R PS (supd PS a P').
Proof.
  induction PS as [|[[p s] P] PS IH]; simpl; intros a P' H; [constructor|].
  destruct (eq_dec p a) as [->|n]; [rewrite if_true by auto | rewrite if_false by auto]; constructor; simpl.
  - destruct (H s P) as [H1 H2]; [rewrite if_true by auto; reflexivity|]. auto.
  - apply hrx5_b8i4_R_refl.
  - auto.
  - apply IH. intros sh P0 Hs. apply (H sh). rewrite if_false by auto. auto.
Qed.

Lemma hrx5_b8i4_R_addr: forall PS PS', Forall2 hrx5_b8i4_R PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  intros PS PS' H; induction H as [|x x' PS PS' Hr HF IH]; [reflexivity|].
  destruct x as [[p s] P], x' as [[p' s'] P']; simpl in *. destruct Hr as [-> _]. f_equal; auto.
Qed.

Lemma hrx5_b8i4_cmp: forall own T PS PS', Forall2 hrx5_b8i4_R PS PS' ->
  Forall (fun x => match x with (p, _, P) =>
            In (hs_addr p) (saddrs (t_D T)) /\
            Forall (vp_ok own) (hs_ptrs (hs_snap_cur T p P) (hs_snap_cur T p P) ++ pr_ptrs P P) end) PS ->
  hn4_cmp_ok own T (hrx5_b8i4_sns T PS) (hrx5_b8i4_prs PS) PS'.
Proof.
  intros own T PS PS' H; induction H as [|x x' PS PS' Hr HF IH]; intros HQ; [exact I|].
  pose proof (Forall_inv HQ) as HQ1. pose proof (Forall_inv_tail HQ) as HQ2.
  destruct x as [[p sh] P], x' as [[p' sh'] P']. simpl in Hr. destruct Hr as (-> & Hs & Hp).
  unfold hrx5_b8i4_sns, hrx5_b8i4_prs. cbn [map hn4_cmp_ok].
  split; [|apply IH; exact HQ2].
  destruct HQ1 as [HI HF1]. split; [exact HI|].
  rewrite Hp. unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of in *. cbn [sn_next sn_entry sn_hs] in *.
  rewrite Hs. exact HF1.
Qed.

Lemma hrx5_b8i4_hs_ok: forall own T wd p P E,
  t_entry T (hs_addr p) = Some E -> e_peer E = p -> In p own -> incl (t_L T) own ->
  hs_sid (p_hs P) = id_addr wd -> In (id_addr wd) own ->
  Forall (vp_ok own) (hs_ptrs (hs_snap_cur T p P) (hs_snap_cur T p P)).
Proof.
  intros own T wd p P E HE He Hp Hi Hs Hid.
  unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of, t_entry_d. rewrite HE. cbn [sn_next sn_entry sn_hs].
  rewrite He, Hs.
  assert (Hn: vp_ok own (succ_in (t_L T) (hs_addr p))).
  { destruct (hrx5_b8i4_succ_in (t_L T) (hs_addr p)) as [H|H]; [left; auto | right; apply Hi; auto]. }
  assert (Hp': vp_ok own p) by (right; exact Hp).
  assert (Hid': vp_ok own (id_addr wd)) by (right; exact Hid).
  repeat apply Forall_cons; try apply Forall_nil; auto.
Qed.

Lemma hrx5_b8i4_same: forall T a PS PS',
  Forall2 (fun x x' => x' = x \/ peer_addr4 x' = a) PS PS' ->
  hnodes_same4 T a (hrx5_b8i4_sns T PS) (hrx5_b8i4_rs PS) (hrx5_b8i4_prs PS) PS' = true.
Proof.
  intros T a PS PS' H; induction H as [|x x' PS PS' Hx _ IH]; [reflexivity|].
  destruct x as [[p sh] P]. unfold hrx5_b8i4_sns, hrx5_b8i4_rs, hrx5_b8i4_prs in *. cbn [map].
  destruct Hx as [->|Ha].
  - cbn [hnodes_same4]. rewrite IH, andb_true_r.
    destruct (eq_dec p a); auto.
    rewrite hrx5_b8i4_snap_eqb_refl, Int.eq_true, hrx5_b8i4_pr_eqb_refl. reflexivity.
  - destruct x' as [[p' sh'] P']; simpl in Ha; subst. cbn [hnodes_same4].
    rewrite IH, andb_true_r, if_true; auto.
Qed.

Lemma hrx5_b8i4_same_refl: forall a (PS: list (val * share * peer)),
  Forall2 (fun x x' => x' = x \/ peer_addr4 x' = a) PS PS.
Proof. induction PS; constructor; auto. Qed.

Lemma hrx5_b8i4_same_supd: forall a P' (PS: list (val * share * peer)),
  Forall2 (fun x x' => x' = x \/ peer_addr4 x' = a) PS (supd PS a P').
Proof.
  induction PS as [|[[p s] P] PS IH]; simpl; [constructor|].
  destruct (eq_dec p a) as [->|n]; [rewrite if_true by auto | rewrite if_false by auto]; constructor; auto.
  apply hrx5_b8i4_same_refl.
Qed.

Lemma hrx5_b8i4_nsplit: forall T NS PS a sh P, map hn_p NS = map peer_addr4 PS -> sfind PS a = Some (sh, P) ->
  exists NS1 N0 NS2, hnodes_snapped4 T NS PS = NS1 ++ N0 :: NS2 /\
    hn_addr N0 = hrx5_nfind NS a /\ hn_p N0 = a.
Proof.
  induction NS as [|N NS IH]; destruct PS as [|[[x s] v] PS]; intros a sh P Hm Hs;
    simpl in Hm, Hs; try discriminate.
  injection Hm as H0 H1. rewrite hrx5_b8i4_snapped_cons. simpl hrx5_nfind. rewrite H0.
  destruct (EqDec_val x a) as [->|n].
  - inv Hs. eexists [], _, (hnodes_snapped4 T NS PS). simpl. auto.
  - destruct (IH PS a sh P H1 Hs) as (NS1 & N0 & NS2 & E1 & E2 & E3).
    exists (hn_snapshot4 T N (x, s, v) :: NS1), N0, NS2. rewrite E1. auto.
Qed.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.

(* the objects lent to hnodes_same_except: D (p_device, hs_sid) and the kents *)
Definition hrx5_b8i4_VO (R: hrx5_run) (L: hrx5_loc) (sec: list byte) (birth: int64) (T: tstate)
  (KE: list kent4) : list vobj :=
  [VDev Tsh (l_wd L) (hrx5_DL x25519 R L sec birth);
   VKents (hrx5_khead (map (kent_snapped T) KE)) (map (kent_snapped T) KE)].

Lemma hrx5_b8i4_VO_addrs R L sec birth T KE :
  vobjs_addrs (hrx5_b8i4_VO R L sec birth T KE) = [l_wd L; id_addr (l_wd L); cc_addr (l_wd L)].
Proof.
  (* v4.1: VKents lends no address *)
  unfold hrx5_b8i4_VO, vobjs_addrs. cbn [map concat vobj_addrs app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma hrx5_b8i4_facts R L sec birth NS PS KE T head nk a P P' :
  hrx5_inv x25519 R L NS PS KE T head nk -> itable_wf T -> sfind PS a = Some (Ews, P) ->
  hs_sid (p_hs P') = hs_sid (p_hs P) -> pr_ptrs P P' = pr_ptrs P P ->
  (exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hrx5_nfind NS a /\ hn_p N = a) /\
  Forall vobj_ok (hrx5_b8i4_VO R L sec birth T KE) /\
  hnodes_peers4 (hnodes_snapped4 T NS PS) (supd PS a P') /\
  peers_wf (supd PS a P') /\
  Zlength (hrx5_b8i4_sns T PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hrx5_b8i4_rs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hrx5_b8i4_prs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hrx5_b8i4_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hrx5_b8i4_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hrx5_b8i4_prs PS) /\
  hn4_cmp_ok (map peer_addr4 (supd PS a P') ++ saddrs (t_D T) ++ vobjs_addrs (hrx5_b8i4_VO R L sec birth T KE)) T
    (hrx5_b8i4_sns T PS) (hrx5_b8i4_prs PS) (supd PS a P') /\
  (a = nullval \/ In a (map peer_addr4 (supd PS a P'))) /\
  hnodes_same4 T a (hrx5_b8i4_sns T PS) (hrx5_b8i4_rs PS) (hrx5_b8i4_prs PS) (supd PS a P') = true /\
  vobj_ok (VPeers (supd PS a P')) /\
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers (supd PS a P')])) (kent_ptrs T e))
    (map (kent_snapped T) KE).
Proof.
  intros Hl Hw Hs Hsid Hpp.
  destruct Hl as (Hpok & Hwf & _ & Hch & Hpeers & _ & Hp).
  pose proof (hrx5_b8i4_peers_len _ _ Hpeers) as Hlen.
  assert (HR: Forall2 hrx5_b8i4_R PS (supd PS a P')).
  { apply hrx5_b8i4_R_supd. intros sh P0 Hs0. rewrite Hs in Hs0. inv Hs0. auto. }
  assert (HA: map peer_addr4 (supd PS a P') = map peer_addr4 PS) by apply hrx5_b8i4_supd_addr.
  pose proof (hrx5cr_model_sfind_in _ _ _ _ Hs) as HinP.
  assert (HinA: In a (map peer_addr4 PS)) by (apply (in_map peer_addr4) in HinP; exact HinP).
  destruct (hrx5_b8i4_snapped_vals T NS PS Hlen) as (H1 & H2 & H3 & H4).
  assert (Hews: Forall (fun x : val * share * peer => match x with (_, sh, _) => readable_share sh end)
                  (supd PS a P')).
  { apply hrx5_b8i4_supd_wf with (a := a) (P' := P') in Hwf. unfold peers_wf in Hwf.
    eapply Forall_impl; [|exact Hwf]. intros [[x sh] Q] Hx. apply writable_readable; exact Hx. }
  split; [apply hrx5_b8i4_nsplit with (sh := Ews) (P := P); auto|].
  split; [unfold hrx5_b8i4_VO; constructor; [simpl; auto | constructor; [exact I | constructor]]|].
  split; [unfold hnodes_peers4; rewrite hrx5_b8i4_snapped_p, HA by auto; exact Hpeers|].
  split; [apply hrx5_b8i4_supd_wf; auto|].
  split; [unfold hrx5_b8i4_sns; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [unfold hrx5_b8i4_rs; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [unfold hrx5_b8i4_prs; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split.
  { apply hrx5_b8i4_cmp; [exact HR|].
    rewrite HA, hrx5_b8i4_VO_addrs.
    pose proof (hrx5_b8i4_pool_entry_wf _ _ _ Hp Hw) as HF.
    pose proof (hrx5_b8i4_chain_next _ _ Hch) as HN.
    destruct Hw as (_ & Hi & _).
    rewrite Forall_forall; intros x Hx.
    pose proof (proj1 (Forall_forall _ _) Hpok x Hx) as Hk.
    pose proof (proj1 (Forall_forall _ _) HF x Hx) as (HI & E & HE & He & _).
    pose proof (proj1 (Forall_forall _ _) HN x Hx) as Hn.
    destruct x as [[p sh] Q]. cbn [peer_addr4] in HI, HE, He. split; [exact HI|].
    destruct Hk as (_ & Hd & Hsd & _ & _ & _ & _ & _ & Hc & Hpv & Hnx).
    apply Forall_app; split.
    - eapply hrx5_b8i4_hs_ok; [exact HE | exact He | | | exact Hsd |].
      + apply in_or_app; left. apply (in_map peer_addr4 PS (p, sh, Q)) in Hx; exact Hx.
      + intros y Hy. apply in_or_app; right; apply in_or_app; left; apply Hi; auto.
      + apply in_or_app; right; apply in_or_app; right; right; left; reflexivity.
    - assert (Hn': vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++
                    [l_wd L; id_addr (l_wd L); cc_addr (l_wd L)]) (p_pknext Q)).
      { eapply hrx5_b8i4_vp_mono; [|exact Hn]. intros y Hy; apply in_or_app; left; exact Hy. }
      assert (Hwd: vp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++
                    [l_wd L; id_addr (l_wd L); cc_addr (l_wd L)]) (l_wd L)).
      { right. apply in_or_app; right; apply in_or_app; right; left; reflexivity. }
      unfold pr_ptrs. rewrite Hd, Hc, Hpv, Hnx.
      repeat apply Forall_cons; try apply Forall_nil; auto; left; reflexivity. }
  split; [right; rewrite HA; exact HinA|].
  split; [apply hrx5_b8i4_same, hrx5_b8i4_same_supd|].
  split; [exact Hews|].
  pose proof (hrx5_b8i4_pool_ke KE PS T Hp Hw) as HK.
  destruct Hw as (_ & Hinc & _ & _).
  apply Forall_forall. intros e' He'. apply in_map_iff in He'. destruct He' as (e & <- & He).
  pose proof (proj1 (Forall_forall _ _) HK e He) as (HinS & Hke).
  assert (Hpe: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers (supd PS a P')]) (e_peer (t_entry_d T (ke_addr e)))).
  { right. apply in_or_app. right. cbn. rewrite app_nil_r, HA. exact Hke. }
  assert (Hn: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers (supd PS a P')]) (succ_in (t_L T) (ke_addr e))).
  { destruct (hrx5_b8i4_succ_in (t_L T) (ke_addr e)) as [-> | Hi]; [left; reflexivity |].
    right. apply in_or_app. left. apply Hinc. exact Hi. }
  unfold kent_snapped, kent_ptrs; cbn.
  split; [exact HinS | split; [discriminate |]].
  repeat (apply Forall_cons; [assumption |]). apply Forall_nil.
Qed.

Lemma hrx5_b8i4_sfind_pk: forall (l: list (val * share * peer)) a sh v,
  NoDup (map peer_addr4 l) -> In (a, sh, v) l -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros a sh v Hn H; [contradiction|].
  inv Hn.
  destruct (eq_dec x a) as [->|n]; [rewrite if_true by auto|rewrite if_false by auto].
  - destruct H as [H|H]; [inv H; reflexivity|].
    exfalso; apply H2. apply (in_map peer_addr4 l (a, sh, v)) in H; exact H.
  - destruct H as [H|H]; [inv H; congruence|]. apply IH; auto.
Qed.

Lemma hrx5_b8i4_sfind R L NS PS KE T head nk a sh P :
  hrx5_inv x25519 R L NS PS KE T head nk -> In (a, sh, P) PS -> sfind PS a = Some (Ews, P).
Proof.
  intros (Hpok & _ & Hnd & _) Hin.
  pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as (Hsh & _). subst sh.
  apply hrx5_b8i4_sfind_pk; auto.
Qed.

End Pure.
