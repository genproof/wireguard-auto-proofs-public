(* law consume_initiation_any, phase P8, segment A2: the pure facts of
   CHECK(hnodes_same_except(peers, target->p)) (port of v1's hci3_p8_A2_pure.v): the arguments sns / rs / prs / VO
   of hnodes_same_except4_spec (what the nodes hold after hnodes_snap, the objects lent), its premises on the
   snapshot nodes and the updated peers, the node of the accepted peer, and the result 1. *)
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Local Open Scope Z_scope.

(* what the nodes hold after hnodes_snap *)
Definition hci5_p8_A2_sns (T: tstate) (PS: list (val * share * peer)) : list hsnap :=
  map (fun x => match x with (p, _, P) => hs_snap_cur T p P end) PS.
Definition hci5_p8_A2_rs (PS: list (val * share * peer)) : list int :=
  map (fun x => match x with (_, _, P) => p_refs P end) PS.
Definition hci5_p8_A2_prs (PS: list (val * share * peer)) : list peer :=
  map (fun x => match x with (_, _, P) => P end) PS.

Ltac hci5_p8_A2_dif := match goal with |- context [if ?d then _ else _] => destruct d end.

Lemma hci5_p8_A2_bytes_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hci5_p8_A2_veqb_refl x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hci5_p8_A2_snap_refl s : snap_eqb s s = true.
Proof.
  destruct s as [[p ty ix] nx hb H]. unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hci5_p8_A2_bytes_refl.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hci5_p8_A2_pr_refl P : pr_eqb P P = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb.
  rewrite ?hci5_p8_A2_veqb_refl, ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hci5_p8_A2_bytes_refl.
  reflexivity.
Qed.

Lemma hci5_p8_A2_snapped_cons T N NS x PS :
  hnodes_snapped4 T (N :: NS) (x :: PS) = hn_snapshot4 T N x :: hnodes_snapped4 T NS PS.
Proof. reflexivity. Qed.

Lemma hci5_p8_A2_snapped_maps T NS PS : length NS = length PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hci5_p8_A2_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hci5_p8_A2_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hci5_p8_A2_prs PS) /\
  length (hnodes_snapped4 T NS PS) = length PS.
Proof.
  revert PS; induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hl; try discriminate; [simpl; auto|].
  injection Hl as Hl. destruct (IH PS Hl) as (H1 & H2 & H3 & H4 & H5).
  rewrite hci5_p8_A2_snapped_cons. destruct x as [[p sh] P]. cbn [map length].
  rewrite H1, H2, H3, H4, H5. simpl. auto.
Qed.

Lemma hci5_p8_A2_peers_len NS PS : hnodes_peers4 NS PS -> length NS = length PS.
Proof.
  intros H. unfold hnodes_peers4 in H.
  rewrite <- (map_length hn_p NS), H, map_length. reflexivity.
Qed.

Lemma hci5_p8_A2_supd_addr (PS: list (val * share * peer)) a P' :
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [|[[x s] w] PS IH]; simpl; auto.
  hci5_p8_A2_dif; simpl; f_equal; auto.
Qed.

Lemma hci5_p8_A2_supd_wf PS a P' : peers_wf PS -> peers_wf (supd PS a P').
Proof.
  unfold peers_wf. induction PS as [|[[x s] w] PS IH]; simpl; intros H; auto.
  inv H. hci5_p8_A2_dif; constructor; auto.
Qed.

(* supd as a pointwise relation *)
Lemma hci5_p8_A2_F2_refl {X: Type} (Rel: X -> X -> Prop) l :
  (forall x, In x l -> Rel x x) -> Forall2 Rel l l.
Proof.
  induction l as [|x l IH]; intros H; constructor.
  - apply H; simpl; auto.
  - apply IH. intros y Hy. apply H; simpl; auto.
Qed.

Lemma hci5_p8_A2_F2_supd (Rel: val * share * peer -> val * share * peer -> Prop) PS a P' :
  (forall x, In x PS -> Rel x x) ->
  (forall p sh P, In (p, sh, P) PS -> p = a -> Rel (p, sh, P) (p, sh, P')) ->
  Forall2 Rel PS (supd PS a P').
Proof.
  induction PS as [|[[p s] P] PS IH]; simpl; intros H1 H2; [constructor|].
  destruct (EqDec_val p a) as [->|n]; constructor.
  - apply H2; auto.
  - apply hci5_p8_A2_F2_refl. intros x Hx. apply H1; auto.
  - apply H1; auto.
  - apply IH; auto.
Qed.

Lemma hci5_p8_A2_cmp_F2 own T PS PS' :
  Forall2 (fun x x' => match x, x' with (_, _, P0), (p, _, P) =>
             (In (hs_addr p) (saddrs (t_D T)) /\
              Forall (vp_ok own) (hs_ptrs (hs_snap_cur T (peer_addr4 x) P0) (hs_snap_cur T p P) ++ pr_ptrs P0 P))
           end) PS PS' ->
  hn4_cmp_ok own T (hci5_p8_A2_sns T PS) (hci5_p8_A2_prs PS) PS'.
Proof.
  intros H; induction H as [|x x' PS PS' Hx _ IH]; [simpl; auto|].
  destruct x as [[p0 s0] P0], x' as [[p s] P]. simpl. split; [exact Hx | exact IH].
Qed.

Lemma hci5_p8_A2_same T a PS PS' :
  Forall2 (fun x x' => x' = x \/ peer_addr4 x' = a) PS PS' ->
  hnodes_same4 T a (hci5_p8_A2_sns T PS) (hci5_p8_A2_rs PS) (hci5_p8_A2_prs PS) PS' = true.
Proof.
  intros H; induction H as [|x x' PS PS' Hx _ IH]; [reflexivity|].
  destruct x' as [[p s] P]. destruct x as [[p0 s0] P0]. unfold hci5_p8_A2_sns, hci5_p8_A2_rs, hci5_p8_A2_prs in *.
  cbn [map hnodes_same4]. rewrite IH, andb_true_r. destruct Hx as [Hx|Ha].
  - inv Hx. destruct (eq_dec p0 a); auto.
    rewrite hci5_p8_A2_snap_refl, Int.eq_true, hci5_p8_A2_pr_refl. reflexivity.
  - simpl in Ha. subst. rewrite if_true; auto.
Qed.

Lemma hci5_p8_A2_split T NS PS a : map hn_p NS = map peer_addr4 PS -> In a (map peer_addr4 PS) ->
  exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hci5_nfind NS a /\ hn_p N = a.
Proof.
  revert PS; induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hm Hin;
    simpl in Hm; try discriminate; [contradiction|].
  injection Hm as H0 H1. rewrite hci5_p8_A2_snapped_cons. simpl hci5_nfind.
  destruct x as [[p sh] P].
  destruct (EqDec_val (hn_p N) a) as [Ha|Ha].
  - exists [], (hn_snapshot4 T N (p, sh, P)), (hnodes_snapped4 T NS PS). simpl. auto.
  - assert (Hin': In a (map peer_addr4 PS)).
    { simpl in Hin. destruct Hin as [Hin|Hin]; auto. simpl in H0. congruence. }
    destruct (IH PS H1 Hin') as (NS1 & N0 & NS2 & E1 & E2 & E3).
    exists (hn_snapshot4 T N (p, sh, P) :: NS1), N0, NS2. rewrite E1. auto.
Qed.

(* the public-key chain: every pknext is NULL or a peer of the list *)
Lemma hci5_p8_A2_chain_hd h PS : pk_chain h PS -> h = nullval \/ In h (map peer_addr4 PS).
Proof.
  destruct PS as [|[[p s] P] PS]; simpl; intros H; [auto|]. destruct H as [-> _]. auto.
Qed.

Lemma hci5_p8_A2_chain h PS : pk_chain h PS ->
  Forall (fun x => match x with (_, _, P) => vp_ok (map peer_addr4 PS) (p_pknext P) end) PS.
Proof.
  revert h; induction PS as [|[[p s] P] PS IH]; simpl; intros h H; [constructor|].
  destruct H as [_ H]. constructor.
  - destruct (hci5_p8_A2_chain_hd _ _ H) as [E|E]; [left; exact E | right; simpl; auto].
  - eapply Forall_impl; [|exact (IH _ H)]. intros [[q t] Q] Hq. destruct Hq as [Hq|Hq]; [left; auto | right; simpl; auto].
Qed.

Lemma hci5_p8_A2_succ_in L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; auto.
  hci5_p8_A2_dif.
  - destruct L; simpl; auto.
  - destruct IH; auto.
Qed.

Lemma hci5_p8_A2_kaddrs T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. reflexivity. Qed.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the objects lent to hnodes_same_except: B's device (p_device, hs_sid) and the kents (keypair slots) *)
Definition hci5_p8_A2_VO (R: hci5_run) (L: hci5_loc) (T: tstate) (KE: list kent4) : list vobj :=
  [VDev Tsh (l_wb L) (hci5_DB x25519 R L); VKents (hci5_khead KE) (map (kent_snapped T) KE)].

Lemma hci5_p8_A2_tgt_In IB PS M now a P t ck2 h2 :
  hci5_tgt x25519 aead_dec IB PS M now = Some (a, P, t, ck2, h2) -> exists sh, In (a, sh, P) PS.
Proof.
  intros H. unfold hci5_tgt in H.
  destruct (mi_ok IB); [|discriminate].
  destruct (m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M)) as [[[[s x] ck1] h1]|];
    [|discriminate].
  destruct (pk_find PS s) as [[a0 P0]|] eqn:Hpk; [|discriminate].
  destruct (m_consume_init2_model _ _ _ _ _) as [[[t0 ck0] h0]|]; [|discriminate].
  destruct (_ && _)%bool; [|discriminate].
  inv H. eapply hci5_model_pk_find; eauto.
Qed.

Lemma hci5_p8_A2_facts R L NS PS KE T head na IB M now a P t ck2 h2 :
  hci5_inv x25519 R L NS PS KE T head na -> itable_wf T ->
  hci5_tgt x25519 aead_dec IB PS M now = Some (a, P, t, ck2, h2) ->
  (exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hci5_nfind NS a /\ hn_p N = a) /\
  Forall vobj_ok (hci5_p8_A2_VO R L T KE) /\
  hnodes_peers4 (hnodes_snapped4 T NS PS) (supd PS a (hci5_p8_put P M now t ck2 h2)) /\
  peers_wf (supd PS a (hci5_p8_put P M now t ck2 h2)) /\
  Zlength (hci5_p8_A2_sns T PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hci5_p8_A2_rs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hci5_p8_A2_prs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hci5_p8_A2_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hci5_p8_A2_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hci5_p8_A2_prs PS) /\
  hn4_cmp_ok (map peer_addr4 (supd PS a (hci5_p8_put P M now t ck2 h2)) ++ saddrs (t_D T) ++
              vobjs_addrs (hci5_p8_A2_VO R L T KE)) T
    (hci5_p8_A2_sns T PS) (hci5_p8_A2_prs PS) (supd PS a (hci5_p8_put P M now t ck2 h2)) /\
  (a = nullval \/ In a (map peer_addr4 (supd PS a (hci5_p8_put P M now t ck2 h2)))) /\
  hnodes_same4 T a (hci5_p8_A2_sns T PS) (hci5_p8_A2_rs PS) (hci5_p8_A2_prs PS)
    (supd PS a (hci5_p8_put P M now t ck2 h2)) = true.
Proof.
  intros Hl Hw Ht.
  destruct Hl as (Hpok & Hwf & Hch & Hpeers & _ & HT & Hslots).
  destruct HT as (HD & _ & HEp & _).
  destruct Hw as (_ & Hincl & _ & _).
  pose proof (hci5_p8_A2_peers_len _ _ Hpeers) as Hlen.
  destruct (hci5_p8_A2_tgt_In _ _ _ _ _ _ _ _ _ Ht) as [shP HinP].
  set (P' := hci5_p8_put P M now t ck2 h2).
  set (PS' := supd PS a P').
  destruct (hci5_p8_A2_snapped_maps T NS PS Hlen) as (H0 & H1 & H2 & H3 & H4).
  assert (HinA: In a (map peer_addr4 PS)) by (apply (in_map peer_addr4) in HinP; exact HinP).
  assert (Hown: forall v, In v (map peer_addr4 PS) \/ In v (saddrs (t_D T)) \/
                          In v [l_wb L; id_addr (l_wb L); cc_addr (l_wb L)] \/ In v (map ke_addr KE) ->
                vp_ok (map peer_addr4 PS' ++ saddrs (t_D T) ++ vobjs_addrs (hci5_p8_A2_VO R L T KE)) v).
  { intros v Hv. right. unfold PS'. rewrite hci5_p8_A2_supd_addr.
    (* v4.1: VKents lends no address; a kent's address is its pool entry (saddrs (t_D T)) *)
    assert (Hk: In v (map ke_addr KE) -> In v (saddrs (t_D T))) by (rewrite HD; intro; apply in_app_iff; left; auto).
    unfold hci5_p8_A2_VO, vobjs_addrs. cbn [map vobj_addrs concat].
    rewrite !in_app_iff. tauto. }
  assert (Hchain := hci5_p8_A2_chain _ _ Hch).
  set (own := map peer_addr4 PS' ++ saddrs (t_D T) ++ vobjs_addrs (hci5_p8_A2_VO R L T KE)) in *.
  assert (Hq: forall p sh Q, In (p, sh, Q) PS ->
            Forall (vp_ok own) [p_device Q; p_cur Q; p_prev Q; p_next Q; p_pknext Q; hs_sid (p_hs Q)]).
  { intros p sh Q Hin.
    pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hk. simpl in Hk.
    destruct Hk as (_ & Hdev & Hsid & _).
    pose proof (proj1 (Forall_forall _ _) Hslots _ Hin) as Hs. simpl in Hs.
    pose proof (proj1 (Forall_forall _ _) Hchain _ Hin) as Hc. simpl in Hc.
    inv Hs. match goal with Hx: Forall _ [_; _] |- _ => inv Hx end.
    match goal with Hx: Forall _ [_] |- _ => inv Hx end.
    rewrite Hdev, Hsid. clearbody own.
    unfold vp_ok at 1 in Hc.
    apply Forall_forall; intros v Hv; simpl in Hv.
    repeat (destruct Hv as [<-|Hv]); try contradiction;
      first [ apply Hown; simpl; tauto
            | match goal with H: ?k = nullval \/ _ |- vp_ok _ ?k =>
                destruct H as [E|E]; [left; exact E | apply Hown; tauto] end ]. }
  assert (Hpt: forall (p p2: val) (sh sh2: share) (Q Q' Q2: peer), In (p, sh, Q) PS -> In (p2, sh2, Q2) PS ->
            p_device Q' = p_device Q2 -> p_cur Q' = p_cur Q2 -> p_prev Q' = p_prev Q2 -> p_next Q' = p_next Q2 ->
            p_pknext Q' = p_pknext Q2 -> hs_sid (p_hs Q') = hs_sid (p_hs Q2) ->
            In (hs_addr p) (saddrs (t_D T)) /\
            Forall (vp_ok own) (hs_ptrs (hs_snap_cur T p Q) (hs_snap_cur T p Q') ++ pr_ptrs Q Q')).
  { intros p p2 sh sh2 Q Q' Q2 Hin Hin2 E1 E2 E3 E4 E5 E6.
    pose proof (proj1 (Forall_forall _ _) HEp _ Hin) as He. simpl in He.
    assert (Hin_a: In (hs_addr p) (saddrs (t_D T))).
    { rewrite HD, in_app_iff. right. apply (in_map (fun x => hs_addr (peer_addr4 x))) in Hin. exact Hin. }
    assert (Hpa: In p (map peer_addr4 PS)) by (apply (in_map peer_addr4) in Hin; exact Hin).
    split; [exact Hin_a|].
    unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of, pr_ptrs. cbn [sn_next sn_entry sn_hs app].
    rewrite E1, E2, E3, E4, E5, E6, He.
    assert (Hsucc: vp_ok own (succ_in (t_L T) (hs_addr p))).
    { destruct (hci5_p8_A2_succ_in (t_L T) (hs_addr p)) as [E|E]; [left; exact E|].
      apply Hown. right; left. apply Hincl, E. }
    assert (Hpo: vp_ok own p) by (apply Hown; tauto).
    pose proof (Hq _ _ _ Hin) as F1. pose proof (Hq _ _ _ Hin2) as F2.
    clearbody own.
    apply Forall_forall. intros v Hv. simpl in Hv.
    rewrite Forall_forall in F1, F2.
    repeat (destruct Hv as [<-|Hv]); try contradiction;
      first [exact Hsucc | exact Hpo | apply F1; simpl; tauto | apply F2; simpl; tauto]. }
  split; [apply hci5_p8_A2_split; auto|].
  split.
  { unfold hci5_p8_A2_VO. repeat constructor; simpl; auto. }
  split; [unfold hnodes_peers4, PS'; rewrite H0, hci5_p8_A2_supd_addr; exact Hpeers|].
  split; [apply hci5_p8_A2_supd_wf; auto|].
  split; [unfold hci5_p8_A2_sns; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [unfold hci5_p8_A2_rs; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [unfold hci5_p8_A2_prs; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split.
  { apply hci5_p8_A2_cmp_F2. unfold PS'. apply hci5_p8_A2_F2_supd.
    - intros [[p sh] Q] Hin. apply (Hpt p p sh sh Q Q Q); auto.
    - intros p sh Q Hin _. apply (Hpt p a sh shP Q P' P); auto;
        unfold P', hci5_p8_put, hci5_new; reflexivity. }
  split; [right; unfold PS'; rewrite hci5_p8_A2_supd_addr; exact HinA|].
  apply hci5_p8_A2_same. unfold PS'. apply hci5_p8_A2_F2_supd; [intros; left; auto | intros; right; simpl; auto].
Qed.

End Pure.
