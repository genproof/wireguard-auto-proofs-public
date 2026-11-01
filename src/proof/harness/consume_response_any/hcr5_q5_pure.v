(* law consume_response_any, phase Q5: the pure facts shared by the segments.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_defs.
Local Open Scope Z_scope.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* a new state P' of the peer at a that keeps what hnodes_same_except / pr_same compare as pointers *)
Definition hcr5_q5_keeps (PS: list (val * share * peer)) (a: val) (P': peer) : Prop :=
  forall sh P0, sfind PS a = Some (sh, P0) ->
    hs_sid (p_hs P') = hs_sid (p_hs P0) /\ pr_ptrs P0 P' = pr_ptrs P0 P0.

Definition hcr5_q5_pure_stmt : Prop :=
  (* 1: the preconditions of hnodes_same_except4 on the snapshot nodes (sns = hcr5_sns T PS, rs = hcr5_rs PS,
     prs = hcr5_prs PS, VO = hcr5_q5_VO: A's device and the kents lent), for the peers PS' = PS, or PS after
     the update of one peer that keeps its pointers *)
  (forall R L NS PS head nb KE T (PS': list (val * share * peer)),
     hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
     (PS' = PS \/ exists a P', PS' = supd PS a P' /\ hcr5_q5_keeps PS a P') ->
     Forall vobj_ok (hcr5_q5_VO x25519 R L T KE) /\
     hnodes_peers4 (hnodes_snapped4 T NS PS) PS' /\ peers_wf PS' /\
     Zlength (hcr5_sns T PS) = Zlength (hnodes_snapped4 T NS PS) /\
     Zlength (hcr5_rs PS) = Zlength (hnodes_snapped4 T NS PS) /\
     Zlength (hcr5_prs PS) = Zlength (hnodes_snapped4 T NS PS) /\
     map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hcr5_sns T PS) /\
     map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hcr5_rs PS) /\
     map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hcr5_prs PS) /\
     hn4_cmp_ok (map peer_addr4 PS' ++ saddrs (t_D T) ++ vobjs_addrs (hcr5_q5_VO x25519 R L T KE)) T
       (hcr5_sns T PS) (hcr5_prs PS) PS') /\
  (* 2: nothing changed: hnodes_same_except(peers, NULL) holds *)
  (forall T PS, hnodes_same4 T nullval (hcr5_sns T PS) (hcr5_rs PS) (hcr5_prs PS) PS = true) /\
  (* 3: only the peer at a changed: hnodes_same_except(peers, a) holds *)
  (forall T PS a P', hnodes_same4 T a (hcr5_sns T PS) (hcr5_rs PS) (hcr5_prs PS) (supd PS a P') = true) /\
  (* 4: the peer the harness's model accepts: its place in the peers and the nodes (with its snapshots), its
     handshake entry, the model's conditions, the pointers pr_same compares (with the other peers lent) *)
  (forall R L NS PS head nb KE T M a P ck h,
     hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
     hcr5_tg x25519 aead_dec R T PS M = Some (a, P, ck, h) ->
     exists NS1 N NS2 PS1 PS2 E,
       PS = PS1 ++ (a, Ews, P) :: PS2 /\ sfind PS a = Some (Ews, P) /\
       (forall P', supd PS a P' = PS1 ++ (a, Ews, P') :: PS2) /\
       hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hcr5_nfind NS a /\ hn_p N = a /\
       hn_snap N = hsnap_val (hs_snap_cur T a P) /\ hn_refs N = Vint (p_refs P) /\ hn_rest N = prsnap_val P /\
       t_entry T (hs_addr a) = Some E /\ e_peer E = a /\ e_type E = IDX_HANDSHAKE /\
       hcr5_pok L (hcr5_ka KE) (a, Ews, P) /\
       mi_ok (hcr5_IA x25519 R) = true /\ hs_state (p_hs P) = HS_CREATED_INITIATION /\
       m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
         (mi_priv (hcr5_IA x25519 R)) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M) = Some (ck, h) /\
       Forall (vp_ok (a :: vobjs_addrs (hcr5_q5_VOp x25519 R L T ++ [VPeers (PS1 ++ PS2)]))) (pr_ptrs P P)) /\
  (* 5: the lists after the call (the kents' snapshot, one peer updated or none) *)
  (forall L KA NS PS T KE a P', hcr5_pool (hcr5_ka KE) PS T -> hnodes_peers4 NS PS -> peers_wf PS ->
     Forall (hcr5_pok L KA) PS ->
     hcr5_pool (hcr5_ka (map (kent_snapped T) KE)) (supd PS a P') T /\
     hcr5_pool (hcr5_ka (map (kent_snapped T) KE)) PS T /\
     hcr5_khead (map (kent_snapped T) KE) = hcr5_khead KE /\
     hnodes_peers4 (hnodes_snapped4 T NS PS) (supd PS a P') /\ hnodes_peers4 (hnodes_snapped4 T NS PS) PS /\
     peers_wf (supd PS a P') /\
     Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) (supd PS a P') /\
     Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) PS) /\
  (* 6: the accepted peer's states keep its pointers *)
  (forall PS a P M ck h, sfind PS a = Some (Ews, P) ->
     hcr5_q5_keeps PS a (hcr5_q5_put P M ck h) /\ pr_eqb P (hcr5_q5_put P M ck h) = true).

(* ---------------------------------------------------------------------- *)
(* Helpers (the port of v1's hcr3_q5_pure.v)                              *)
(* ---------------------------------------------------------------------- *)

Ltac hq5_dif := match goal with |- context [if ?d then _ else _] => destruct d end.

Lemma hq5_snap_eqb_refl: forall s, snap_eqb s s = true.
Proof.
  intros [[p ty ix] nx hb H]. unfold snap_eqb, entry_eqb, hs_eqb, bytes_eqb; simpl.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hq5_pr_eqb_refl: forall P, pr_eqb P P = true.
Proof.
  intros P. unfold pr_eqb, pr_eqb_nc, cookie_eqb, veqb, bytes_eqb.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hq5_In_sfind: forall (l: list (val * share * entry)) a sh v,
  In (a, sh, v) l -> exists sh' v', sfind l a = Some (sh', v').
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros a sh v H; [contradiction|].
  destruct (eq_dec x a) as [->|n]; [rewrite if_true by auto; eauto|rewrite if_false by auto].
  destruct H as [H|H]; [inv H; congruence | eauto].
Qed.

Lemma hq5_sfind_nodup: forall (l: list (val * share * entry)) a sh v,
  NoDup (saddrs l) -> In (a, sh, v) l -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros a sh v Hn H; [contradiction|].
  unfold saddrs in Hn; simpl in Hn; inv Hn.
  destruct (eq_dec x a) as [->|n]; [rewrite if_true by auto|rewrite if_false by auto].
  - destruct H as [H|H]; [inv H; reflexivity|].
    exfalso; apply H2. apply (in_map (fun '(x, _, _) => x) l (a, sh, v)) in H; exact H.
  - destruct H as [H|H]; [inv H; congruence|]. apply IH; auto.
Qed.

Lemma hq5_hs_in: forall D PS l, Forall2 hcr5_hs_ok PS l -> incl l D ->
  Forall (fun x => exists E, In (hs_addr (peer_addr4 x), Ews, E) D /\ e_peer E = peer_addr4 x /\
                            e_type E = IDX_HANDSHAKE) PS.
Proof.
  intros D PS l H; induction H as [|y x PS0 l0 Hyx HF IH]; intros Hi; constructor.
  - destruct y as [[p sh] P], x as [[a s] E]; simpl in Hyx. destruct Hyx as (-> & -> & HE & Ht).
    exists E. simpl. split; [apply Hi; left; reflexivity | auto].
  - apply IH. intros z Hz; apply Hi; right; auto.
Qed.

Lemma hq5_pool_in: forall KA PS T, hcr5_pool KA PS T ->
  Forall (fun x => exists E, In (hs_addr (peer_addr4 x), Ews, E) (t_D T) /\ e_peer E = peer_addr4 x /\
                            e_type E = IDX_HANDSHAKE) PS.
Proof.
  intros KA PS T (_ & H). eapply hq5_hs_in; [exact H|].
  intros y Hy. rewrite <- (firstn_skipn (length KA) (t_D T)). apply in_or_app; right; auto.
Qed.

(* every peer's handshake entry: in the pool, found, of the peer, a handshake entry *)
Lemma hq5_pool_entry_wf: forall KA PS T, hcr5_pool KA PS T -> itable_wf T ->
  Forall (fun x => In (hs_addr (peer_addr4 x)) (saddrs (t_D T)) /\
                   exists E, t_entry T (hs_addr (peer_addr4 x)) = Some E /\ e_peer E = peer_addr4 x /\
                            e_type E = IDX_HANDSHAKE) PS.
Proof.
  intros KA PS T Hp (_ & _ & Hn & _). eapply Forall_impl; [|apply (hq5_pool_in _ _ _ Hp)].
  intros x (E & HI & H1 & H2). split.
  - apply (in_map (fun '(x, _, _) => x) (t_D T) _) in HI; exact HI.
  - exists E. unfold t_entry. rewrite (hq5_sfind_nodup _ _ _ _ Hn HI). auto.
Qed.

Lemma hq5_snapped_cons: forall T N NS x PS,
  hnodes_snapped4 T (N :: NS) (x :: PS) = hn_snapshot4 T N x :: hnodes_snapped4 T NS PS.
Proof. reflexivity. Qed.

Lemma hq5_snapped_p: forall T NS PS, length NS = length PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hl; try discriminate; [reflexivity|].
  rewrite hq5_snapped_cons. simpl. rewrite IH by auto. destruct x as [[p sh] P]; reflexivity.
Qed.

Lemma hq5_peers_len: forall NS PS, hnodes_peers4 NS PS -> length NS = length PS.
Proof.
  intros NS PS H. unfold hnodes_peers4 in H.
  rewrite <- (map_length hn_p NS), H, map_length. reflexivity.
Qed.

Lemma hq5_snapped_vals: forall T NS PS, length NS = length PS ->
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hcr5_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hcr5_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hcr5_prs PS) /\
  length (hnodes_snapped4 T NS PS) = length PS.
Proof.
  induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hl; try discriminate; [auto|].
  destruct (IH PS) as (H1 & H2 & H3 & H4); [simpl in Hl; lia|].
  rewrite hq5_snapped_cons. destruct x as [[p sh] P].
  cbn [map length hcr5_sns hcr5_rs hcr5_prs] in *. unfold hcr5_sns, hcr5_rs, hcr5_prs in *.
  cbn [map]. rewrite H1, H2, H3, H4. auto.
Qed.

Lemma hq5_supd_addr: forall (PS: list (val * share * peer)) a P',
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [|[[x s] w] PS IH]; simpl; intros; auto.
  hq5_dif; simpl; f_equal; auto.
Qed.

Lemma hq5_supd_paddr: forall (PS: list (val * share * peer)) a P',
  map hcr5_paddr (supd PS a P') = map hcr5_paddr PS.
Proof.
  induction PS as [|[[x s] w] PS IH]; simpl; intros; auto.
  hq5_dif; simpl; f_equal; auto.
Qed.

Lemma hq5_supd_wf: forall PS a P', peers_wf PS -> peers_wf (supd PS a P').
Proof.
  unfold peers_wf. induction PS as [|[[x s] w] PS IH]; simpl; intros a P' H; auto.
  inv H. hq5_dif; constructor; auto.
Qed.

Lemma hq5_supd_ews: forall PS a P',
  Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) PS ->
  Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) (supd PS a P').
Proof.
  induction PS as [|[[x s] w] PS IH]; simpl; intros a P' H; auto.
  inv H. hq5_dif; constructor; auto.
Qed.

Lemma hq5_supd_hs: forall PS l a P', Forall2 hcr5_hs_ok PS l -> Forall2 hcr5_hs_ok (supd PS a P') l.
Proof.
  intros PS l a P' H; induction H as [|y x PS0 l0 Hyx HF IH]; simpl; [constructor|].
  destruct y as [[p s] w]. hq5_dif; constructor; auto.
Qed.

Lemma hq5_ka_snapped: forall T KE, hcr5_ka (map (kent_snapped T) KE) = hcr5_ka KE.
Proof. intros T KE. unfold hcr5_ka. rewrite map_map. reflexivity. Qed.

Lemma hq5_khead_snapped: forall T KE, hcr5_khead (map (kent_snapped T) KE) = hcr5_khead KE.
Proof. intros T [|e KE]; reflexivity. Qed.

Lemma hq5_pool_supd: forall KA PS T a P', hcr5_pool KA PS T -> hcr5_pool KA (supd PS a P') T.
Proof.
  intros KA PS T a P' (H1 & H2). split; [|apply hq5_supd_hs; auto].
  eapply Forall2_impl; [|exact H1]. intros k [[x sh] E]; simpl. rewrite hq5_supd_paddr. auto.
Qed.

Lemma hq5_succ_in: forall L a, succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; intros a; auto.
  hq5_dif.
  - destruct L; simpl; auto.
  - destruct (IH a); auto.
Qed.

Lemma hq5_vp_mono: forall own own' x, incl own own' -> vp_ok own x -> vp_ok own' x.
Proof. intros own own' x Hi [H|H]; [left; auto | right; auto]. Qed.

Lemma hq5_chain_head: forall head PS, pk_chain head PS -> vp_ok (map peer_addr4 PS) head.
Proof.
  intros head [|[[a s] P] PS]; simpl; intros H; [left; auto | right; left; symmetry; apply H].
Qed.

Lemma hq5_chain_next: forall head PS, pk_chain head PS ->
  Forall (fun x => match x with (_, _, P) => vp_ok (map peer_addr4 PS) (p_pknext P) end) PS.
Proof.
  intros head PS; revert head; induction PS as [|[[a s] P] PS IH]; intros head H; constructor.
  - destruct H as [_ H]. eapply hq5_vp_mono; [|apply (hq5_chain_head _ _ H)].
    intros y Hy; right; auto.
  - destruct H as [_ H]. eapply Forall_impl; [|apply (IH _ H)].
    intros [[b t] Q] Hb. eapply hq5_vp_mono; [|exact Hb]. intros y Hy; right; auto.
Qed.

Lemma hq5_chain_split: forall PS1 head a sh P PS2, pk_chain head (PS1 ++ (a, sh, P) :: PS2) ->
  pk_chain (p_pknext P) PS2.
Proof.
  induction PS1 as [|[[b t] Q] PS1 IH]; simpl; intros head a sh P PS2 H; [apply H|].
  destruct H as [_ H]. eapply IH; exact H.
Qed.

(* the pointers pr_same compares, for a peer of A *)
Lemma hq5_pr_ok: forall own L KA x, hcr5_pok L KA x -> In (l_wa L) own -> incl KA own ->
  vp_ok own (p_pknext (match x with (_, _, P) => P end)) ->
  Forall (vp_ok own) (pr_ptrs (match x with (_, _, P) => P end) (match x with (_, _, P) => P end)).
Proof.
  intros own L KA [[a sh] P] (_ & _ & Hd & _ & _ & _ & Hs) Hw Hk Hn. cbv iota in Hn |- *.
  inv Hs. inv H2. inv H4.
  assert (Hv: forall v, v = nullval \/ In v KA -> vp_ok own v).
  { intros v [Hv|Hv]; [left; auto | right; auto]. }
  assert (Hw': vp_ok own (l_wa L)) by (right; exact Hw).
  unfold pr_ptrs. rewrite Hd.
  repeat apply Forall_cons; try apply Forall_nil; auto.
Qed.

Lemma hq5_vobjs_addrs_app: forall VO1 VO2, vobjs_addrs (VO1 ++ VO2) = vobjs_addrs VO1 ++ vobjs_addrs VO2.
Proof. intros. unfold vobjs_addrs. rewrite map_app, concat_app. reflexivity. Qed.

Lemma hq5_VO_addrs: forall x R L T KE,
  vobjs_addrs (hcr5_q5_VO x R L T KE) = [l_wa L; id_addr (l_wa L); cc_addr (l_wa L)].
Proof. intros. unfold hcr5_q5_VO, vobjs_addrs. cbn [map concat vobj_addrs app]. reflexivity. Qed.

Lemma hq5_VOp_addrs: forall x R L T,
  vobjs_addrs (hcr5_q5_VOp x R L T) = [l_wa L; id_addr (l_wa L); cc_addr (l_wa L); l_ita L] ++ saddrs (t_D T).
Proof. intros. unfold hcr5_q5_VOp, vobjs_addrs. cbn [map concat vobj_addrs app]. rewrite app_nil_r. reflexivity. Qed.

(* the kents' addresses are pool addresses *)
Lemma hq5_ka_in: forall KA PS T, hcr5_pool KA PS T -> incl KA (saddrs (t_D T)).
Proof.
  intros KA PS T [H _] k Hk.
  assert (Hin: forall l1 l2, Forall2 (hcr5_ke_ok PS) l1 l2 -> In k l1 -> In k (saddrs l2)).
  { induction 1 as [|k0 [[a0 s0] E0] l1 l2 Hk0 _ IH]; [simpl; tauto|].
    destruct Hk0 as (Ha & _). subst a0. simpl. intros [E|H']; [left; exact E | right; auto]. }
  specialize (Hin _ _ H Hk).
  rewrite <- (firstn_skipn (length KA) (t_D T)). unfold saddrs in *. rewrite map_app. apply in_or_app; left. exact Hin.
Qed.

(* the relation between the peers PS and PS' (the same, or one updated keeping its pointers) *)
Definition hq5_R (x x': val * share * peer) : Prop :=
  match x, x' with (p, _, P), (p', _, P') =>
    p' = p /\ hs_sid (p_hs P') = hs_sid (p_hs P) /\ pr_ptrs P P' = pr_ptrs P P end.

Lemma hq5_R_refl: forall PS, Forall2 hq5_R PS PS.
Proof. induction PS as [|[[p s] P] PS IH]; constructor; simpl; auto. Qed.

Lemma hq5_R_supd: forall PS a P', hcr5_q5_keeps PS a P' -> Forall2 hq5_R PS (supd PS a P').
Proof.
  unfold hcr5_q5_keeps.
  induction PS as [|[[p s] P] PS IH]; simpl; intros a P' H; [constructor|].
  destruct (eq_dec p a) as [->|n]; [rewrite if_true by auto | rewrite if_false by auto]; constructor; simpl.
  - destruct (H s P) as [H1 H2]; [rewrite if_true by auto; reflexivity|]. auto.
  - apply hq5_R_refl.
  - auto.
  - apply IH. intros sh P0 Hs. apply (H sh). rewrite if_false by auto. auto.
Qed.

Lemma hq5_R_addr: forall PS PS', Forall2 hq5_R PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  intros PS PS' H; induction H as [|x x' PS PS' Hr HF IH]; [reflexivity|].
  destruct x as [[p s] P], x' as [[p' s'] P']; simpl in *. destruct Hr as [-> _]. f_equal; auto.
Qed.

Lemma hq5_cmp: forall own T PS PS', Forall2 hq5_R PS PS' ->
  Forall (fun x => match x with (p, _, P) =>
            In (hs_addr p) (saddrs (t_D T)) /\
            Forall (vp_ok own) (hs_ptrs (hs_snap_cur T p P) (hs_snap_cur T p P) ++ pr_ptrs P P) end) PS ->
  hn4_cmp_ok own T (hcr5_sns T PS) (hcr5_prs PS) PS'.
Proof.
  intros own T PS PS' H; induction H as [|x x' PS PS' Hr HF IH]; intros HQ; [exact I|].
  pose proof (Forall_inv HQ) as HQ1. pose proof (Forall_inv_tail HQ) as HQ2.
  destruct x as [[p sh] P], x' as [[p' sh'] P']. simpl in Hr. destruct Hr as (-> & Hs & Hp).
  unfold hcr5_sns, hcr5_prs. cbn [map hn4_cmp_ok].
  split; [|apply IH; exact HQ2].
  destruct HQ1 as [HI HF1]. split; [exact HI|].
  rewrite Hp. unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of in *. cbn [sn_next sn_entry sn_hs] in *.
  rewrite Hs. exact HF1.
Qed.

(* the hs_ptrs of a peer's current snapshot are valid *)
Lemma hq5_hs_ok: forall own T L p P E,
  t_entry T (hs_addr p) = Some E -> e_peer E = p -> In p own -> incl (t_L T) own ->
  hs_sid (p_hs P) = id_addr (l_wa L) -> In (id_addr (l_wa L)) own ->
  Forall (vp_ok own) (hs_ptrs (hs_snap_cur T p P) (hs_snap_cur T p P)).
Proof.
  intros own T L p P E HE He Hp Hi Hs Hid.
  unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of, t_entry_d. rewrite HE. cbn [sn_next sn_entry sn_hs].
  rewrite He, Hs.
  assert (Hn: vp_ok own (succ_in (t_L T) (hs_addr p))).
  { destruct (hq5_succ_in (t_L T) (hs_addr p)) as [H|H]; [left; auto | right; apply Hi; auto]. }
  assert (Hp': vp_ok own p) by (right; exact Hp).
  assert (Hid': vp_ok own (id_addr (l_wa L))) by (right; exact Hid).
  repeat apply Forall_cons; try apply Forall_nil; auto.
Qed.

Lemma hq5_f1: forall R L NS PS head nb KE T (PS': list (val * share * peer)),
  hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
  (PS' = PS \/ exists a P', PS' = supd PS a P' /\ hcr5_q5_keeps PS a P') ->
  Forall vobj_ok (hcr5_q5_VO x25519 R L T KE) /\
  hnodes_peers4 (hnodes_snapped4 T NS PS) PS' /\ peers_wf PS' /\
  Zlength (hcr5_sns T PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hcr5_rs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hcr5_prs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hcr5_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hcr5_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hcr5_prs PS) /\
  hn4_cmp_ok (map peer_addr4 PS' ++ saddrs (t_D T) ++ vobjs_addrs (hcr5_q5_VO x25519 R L T KE)) T
    (hcr5_sns T PS) (hcr5_prs PS) PS'.
Proof.
  intros R L NS PS head nb KE T PS' Hl Hp Hw HPS'.
  destruct Hl as (Hpok & Hwf & Hch & Hpeers & _ & _).
  pose proof (hq5_peers_len _ _ Hpeers) as Hlen.
  assert (HX: Forall2 hq5_R PS PS' /\ peers_wf PS').
  { destruct HPS' as [->|(a & P' & -> & Hk)].
    - split; [apply hq5_R_refl | auto].
    - split; [apply hq5_R_supd; auto | apply hq5_supd_wf; auto]. }
  destruct HX as [HR Hwf'].
  destruct (hq5_snapped_vals T NS PS Hlen) as (H1 & H2 & H3 & H4).
  assert (Z1: Zlength (hcr5_sns T PS) = Zlength (hnodes_snapped4 T NS PS)).
  { unfold hcr5_sns. rewrite !Zlength_correct, map_length, H4. reflexivity. }
  assert (Z2: Zlength (hcr5_rs PS) = Zlength (hnodes_snapped4 T NS PS)).
  { unfold hcr5_rs. rewrite !Zlength_correct, map_length, H4. reflexivity. }
  assert (Z3: Zlength (hcr5_prs PS) = Zlength (hnodes_snapped4 T NS PS)).
  { unfold hcr5_prs. rewrite !Zlength_correct, map_length, H4. reflexivity. }
  split; [unfold hcr5_q5_VO; constructor; [simpl; auto | constructor; [exact I | constructor]]|].
  split.
  { unfold hnodes_peers4. rewrite hq5_snapped_p by auto. rewrite (hq5_R_addr _ _ HR). exact Hpeers. }
  do 7 (split; [assumption|]).
  apply hq5_cmp; [exact HR|].
  rewrite (hq5_R_addr _ _ HR), hq5_VO_addrs.
  pose proof (hq5_pool_entry_wf _ _ _ Hp Hw) as HF.
  pose proof (hq5_chain_next _ _ Hch) as HN.
  destruct Hw as (_ & Hi & _).
  rewrite Forall_forall; intros x Hx.
  pose proof (proj1 (Forall_forall _ _) Hpok x Hx) as Hk.
  pose proof (proj1 (Forall_forall _ _) HF x Hx) as (HI & E & HE & He & _).
  pose proof (proj1 (Forall_forall _ _) HN x Hx) as Hn.
  destruct x as [[p sh] P]. cbn [peer_addr4] in HI, HE, He. split; [exact HI|].
  apply Forall_app; split.
  - eapply hq5_hs_ok; [exact HE | exact He | | | apply Hk |].
    + apply in_or_app; left. apply (in_map peer_addr4 PS (p, sh, P)) in Hx; exact Hx.
    + intros y Hy. apply in_or_app; right; apply in_or_app; left; apply Hi; auto.
    + apply in_or_app; right; apply in_or_app; right; right; left; reflexivity.
  - eapply (hq5_pr_ok _ L (hcr5_ka KE) (p, sh, P)); [exact Hk | | |].
    + apply in_or_app; right; apply in_or_app; right; left; reflexivity.
    + intros y Hy. apply in_or_app; right; apply in_or_app; left; exact (hq5_ka_in _ _ _ Hp y Hy).
    + cbv iota. eapply hq5_vp_mono; [|exact Hn]. intros y Hy; apply in_or_app; left; exact Hy.
Qed.

Lemma hq5_same: forall T a PS PS',
  Forall2 (fun x x' => x' = x \/ peer_addr4 x' = a) PS PS' ->
  hnodes_same4 T a (hcr5_sns T PS) (hcr5_rs PS) (hcr5_prs PS) PS' = true.
Proof.
  intros T a PS PS' H; induction H as [|x x' PS PS' Hx _ IH]; [reflexivity|].
  destruct x as [[p sh] P]. unfold hcr5_sns, hcr5_rs, hcr5_prs in *. cbn [map].
  destruct Hx as [->|Ha].
  - cbn [hnodes_same4]. rewrite IH, andb_true_r.
    destruct (eq_dec p a); auto.
    rewrite hq5_snap_eqb_refl, Int.eq_true, hq5_pr_eqb_refl. reflexivity.
  - destruct x' as [[p' sh'] P']; simpl in Ha; subst. cbn [hnodes_same4].
    rewrite IH, andb_true_r, if_true; auto.
Qed.

Lemma hq5_same_refl: forall a (PS: list (val * share * peer)),
  Forall2 (fun x x' => x' = x \/ peer_addr4 x' = a) PS PS.
Proof. induction PS; constructor; auto. Qed.

Lemma hq5_same_supd: forall a P' (PS: list (val * share * peer)),
  Forall2 (fun x x' => x' = x \/ peer_addr4 x' = a) PS (supd PS a P').
Proof.
  induction PS as [|[[p s] P] PS IH]; simpl; [constructor|].
  destruct (eq_dec p a) as [->|n]; [rewrite if_true by auto | rewrite if_false by auto]; constructor; auto.
  apply hq5_same_refl.
Qed.

(* the first peer at a: PS = PS1 ++ (a, sh, P) :: PS2 *)
Lemma hq5_psplit: forall (PS: list (val * share * peer)) a sh P, sfind PS a = Some (sh, P) ->
  exists PS1 PS2, PS = PS1 ++ (a, sh, P) :: PS2 /\ (forall P', supd PS a P' = PS1 ++ (a, sh, P') :: PS2).
Proof.
  induction PS as [|[[x s] v] PS IH]; simpl; intros a sh P Hs; [discriminate|].
  destruct (EqDec_val x a) as [->|n].
  - inv Hs. exists [], PS. split; [reflexivity|]. intros P'. reflexivity.
  - destruct (IH a sh P Hs) as (PS1 & PS2 & E1 & E2). exists ((x, s, v) :: PS1), PS2. split.
    + rewrite E1. reflexivity.
    + intros P'. rewrite E2. reflexivity.
Qed.

Lemma hq5_nsplit: forall T NS PS a sh P, map hn_p NS = map peer_addr4 PS -> sfind PS a = Some (sh, P) ->
  exists NS1 N0 NS2, hnodes_snapped4 T NS PS = NS1 ++ hn_snapshot4 T N0 (a, sh, P) :: NS2 /\
    hn_addr N0 = hcr5_nfind NS a /\ hn_p N0 = a.
Proof.
  induction NS as [|N NS IH]; destruct PS as [|[[x s] v] PS]; intros a sh P Hm Hs;
    simpl in Hm, Hs; try discriminate.
  injection Hm as H0 H1. rewrite hq5_snapped_cons. simpl hcr5_nfind. rewrite H0.
  destruct (EqDec_val x a) as [->|n].
  - inv Hs. exists [], N, (hnodes_snapped4 T NS PS). auto.
  - destruct (IH PS a sh P H1 Hs) as (NS1 & N0 & NS2 & E1 & E2 & E3).
    exists (hn_snapshot4 T N (x, s, v) :: NS1), N0, NS2. rewrite E1. auto.
Qed.

Lemma hq5_f4: forall R L NS PS head nb KE T M a P ck h,
  hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> itable_wf T ->
  hcr5_tg x25519 aead_dec R T PS M = Some (a, P, ck, h) ->
  exists NS1 N NS2 PS1 PS2 E,
    PS = PS1 ++ (a, Ews, P) :: PS2 /\ sfind PS a = Some (Ews, P) /\
    (forall P', supd PS a P' = PS1 ++ (a, Ews, P') :: PS2) /\
    hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hcr5_nfind NS a /\ hn_p N = a /\
    hn_snap N = hsnap_val (hs_snap_cur T a P) /\ hn_refs N = Vint (p_refs P) /\ hn_rest N = prsnap_val P /\
    t_entry T (hs_addr a) = Some E /\ e_peer E = a /\ e_type E = IDX_HANDSHAKE /\
    hcr5_pok L (hcr5_ka KE) (a, Ews, P) /\
    mi_ok (hcr5_IA x25519 R) = true /\ hs_state (p_hs P) = HS_CREATED_INITIATION /\
    m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
      (mi_priv (hcr5_IA x25519 R)) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M) = Some (ck, h) /\
    Forall (vp_ok (a :: vobjs_addrs (hcr5_q5_VOp x25519 R L T ++ [VPeers (PS1 ++ PS2)]))) (pr_ptrs P P).
Proof.
  intros R L NS PS head nb KE T M a P ck h Hl Hp Hw Ht.
  destruct Hl as (Hpok & Hwf & Hch & Hpeers & _ & _).
  unfold hcr5_tg, hcr5_tgt in Ht. cbv zeta in Ht.
  destruct (mi_ok (hcr5_IA x25519 R)) eqn:Hok; [|discriminate].
  destruct (t_find_index T (t_L T) (rm_receiver M)) as [[a0 E0]|]; [|discriminate].
  destruct (Int.eq (e_type E0) IDX_HANDSHAKE); [|discriminate].
  destruct (sfind PS (e_peer E0)) as [[sh P0]|] eqn:Hs; [|discriminate].
  destruct (Int.eq (hs_state (p_hs P0)) HS_CREATED_INITIATION) eqn:Hst; [|discriminate].
  destruct (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P0)) (hs_hash (p_hs P0))
              (hs_eph (p_hs P0)) (mi_priv (hcr5_IA x25519 R)) (hs_psk (p_hs P0)) (rm_eph M) (rm_encn M))
    as [[ck0 h0]|] eqn:Hm; [|discriminate].
  injection Ht as <- <- <- <-.
  pose proof (hcr5_model_sfind_in _ _ _ _ Hs) as HIn.
  pose proof (proj1 (Forall_forall _ _) Hpok _ HIn) as Hk.
  assert (sh = Ews) as -> by (simpl in Hk; tauto).
  destruct (hq5_psplit PS (e_peer E0) Ews P0 Hs) as (PS1 & PS2 & HPS & Hsupd).
  destruct (hq5_nsplit T NS PS (e_peer E0) Ews P0 Hpeers Hs) as (NS1 & N0 & NS2 & Hsp & Ha & Hpn).
  pose proof (proj1 (Forall_forall _ _) (hq5_pool_entry_wf _ _ _ Hp Hw) _ HIn) as (_ & E & HE & He & Hty).
  cbn [peer_addr4] in HE, He, Hty.
  exists NS1, (hn_snapshot4 T N0 (e_peer E0, Ews, P0)), NS2, PS1, PS2, E.
  split; [exact HPS | split; [exact Hs | split; [exact Hsupd | split; [exact Hsp |]]]].
  split; [exact Ha | split; [exact Hpn | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]]].
  split; [exact HE | split; [exact He | split; [exact Hty | split; [exact Hk | split; [reflexivity |]]]]].
  split; [apply Int.same_if_eq; auto | split; [exact Hm |]].
  rewrite hq5_vobjs_addrs_app, hq5_VOp_addrs, <- app_assoc. cbn [app].
  apply (hq5_pr_ok _ L (hcr5_ka KE) (e_peer E0, Ews, P0)); [exact Hk | | |].
  - right; left; reflexivity.
  - intros y Hy. do 5 right. apply in_or_app; left; exact (hq5_ka_in _ _ _ Hp y Hy).
  - cbv iota. rewrite HPS in Hch. pose proof (hq5_chain_head _ _ (hq5_chain_split _ _ _ _ _ _ Hch)) as Hn.
    eapply hq5_vp_mono; [|exact Hn]. intros y Hy. do 5 right.
    apply in_or_app; right. unfold vobjs_addrs. cbn [map vobj_addrs concat]. rewrite app_nil_r, map_app.
    apply in_or_app; right; exact Hy.
Qed.

Lemma hcr5_q5_pure_ok : hcr5_q5_pure_stmt.
Proof.
  unfold hcr5_q5_pure_stmt. split; [|split; [|split; [|split; [|split]]]].
  - (* 1 *)
    intros R L NS PS head nb KE T PS' Hl Hp Hw HPS'. exact (hq5_f1 R L NS PS head nb KE T PS' Hl Hp Hw HPS').
  - (* 2 *)
    intros T PS. apply hq5_same, hq5_same_refl.
  - (* 3 *)
    intros T PS a P'. apply hq5_same, hq5_same_supd.
  - (* 4 *)
    intros R L NS PS head nb KE T M a P ck h Hl Hp Hw Ht. exact (hq5_f4 R L NS PS head nb KE T M a P ck h Hl Hp Hw Ht).
  - (* 5 *)
    intros L KA NS PS T KE a P' Hp Hpeers Hwf Hpok.
    pose proof (hq5_peers_len _ _ Hpeers) as Hlen.
    assert (Hq: map hn_p (hnodes_snapped4 T NS PS) = map peer_addr4 PS).
    { rewrite hq5_snapped_p by auto. exact Hpeers. }
    assert (He: Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) PS).
    { eapply Forall_impl; [|exact Hpok]. intros [[x sh] P] Hk. simpl in Hk. tauto. }
    unfold hnodes_peers4. rewrite hq5_supd_addr, hq5_ka_snapped, hq5_khead_snapped.
    split; [apply hq5_pool_supd; auto | split; [auto | split; [auto | split; [exact Hq | split; [exact Hq |]]]]].
    split; [apply hq5_supd_wf; auto | split; [apply hq5_supd_ews; auto | exact He]].
  - (* 6 *)
    intros PS a P M ck h Hs. split.
    + intros sh P0 Hs0. rewrite Hs in Hs0. inv Hs0. split; reflexivity.
    + transitivity (pr_eqb P P); [reflexivity | apply hq5_pr_eqb_refl].
Qed.

End Pure.
