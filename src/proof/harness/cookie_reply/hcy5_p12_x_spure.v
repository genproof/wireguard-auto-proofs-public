(* law cookie_reply, phase P12, segment X, branch target != NULL: the pure facts.
   The target cnode (field n = nd), its node N (the snapshot of the consumed peer a), the peers after the
   consumption split around a (P -> P': only the cookie changed), and the preconditions / results of the three
   comparison calls: hnodes_same_except(peers, a) (sns / rs / prs / VO as consume_initiation's hci5_p8_A2),
   hs_same(&N.snap, &a->handshake) (whole = true, VO lent), pr_same_but_cookie(&N.rest, a) (VO ++ the other
   peers lent).  Helpers: prefix hcy5_p12_x_spure_. *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Local Open Scope Z_scope.

(* what the nodes hold after hnodes_snap *)
Definition hcy5_p12_x_sns (T: tstate) (PS: list (val * share * peer)) : list hsnap :=
  map (fun x => match x with (p, _, P) => hs_snap_cur T p P end) PS.
Definition hcy5_p12_x_rs (PS: list (val * share * peer)) : list int :=
  map (fun x => match x with (_, _, P) => p_refs P end) PS.
Definition hcy5_p12_x_prs (PS: list (val * share * peer)) : list peer :=
  map (fun x => match x with (_, _, P) => P end) PS.

Ltac hcy5_p12_x_spure_dif := match goal with |- context [if ?d then _ else _] => destruct d end.

Lemma hcy5_p12_x_spure_bytes_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hcy5_p12_x_spure_veqb_refl x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hcy5_p12_x_spure_snap_refl s : snap_eqb s s = true.
Proof.
  destruct s as [[p ty ix] nx hb H]. unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hcy5_p12_x_spure_bytes_refl.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hcy5_p12_x_spure_pr_refl P : pr_eqb P P = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb.
  rewrite ?hcy5_p12_x_spure_veqb_refl, ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hcy5_p12_x_spure_bytes_refl.
  reflexivity.
Qed.

Lemma hcy5_p12_x_spure_pr_nc P c : pr_eqb_nc P (p_set_cookie P c) = true.
Proof.
  unfold pr_eqb_nc, p_set_cookie; cbn [p_device p_dead p_cur p_prev p_next p_lsh p_id p_pknext].
  rewrite ?hcy5_p12_x_spure_veqb_refl, ?Int64.eq_true, ?Bool.eqb_reflx. reflexivity.
Qed.

Lemma hcy5_p12_x_spure_snapped_cons T N NS x PS :
  hnodes_snapped4 T (N :: NS) (x :: PS) = hn_snapshot4 T N x :: hnodes_snapped4 T NS PS.
Proof. reflexivity. Qed.

Lemma hcy5_p12_x_spure_snapped_maps T NS PS : length NS = length PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hcy5_p12_x_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hcy5_p12_x_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hcy5_p12_x_prs PS) /\
  length (hnodes_snapped4 T NS PS) = length PS.
Proof.
  revert PS; induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hl; try discriminate; [simpl; auto|].
  injection Hl as Hl. destruct (IH PS Hl) as (H1 & H2 & H3 & H4 & H5).
  rewrite hcy5_p12_x_spure_snapped_cons. destruct x as [[p sh] P]. cbn [map length].
  rewrite H1, H2, H3, H4, H5. simpl. auto.
Qed.

Lemma hcy5_p12_x_spure_peers_len NS PS : hnodes_peers4 NS PS -> length NS = length PS.
Proof.
  intros H. unfold hnodes_peers4 in H.
  rewrite <- (map_length hn_p NS), H, map_length. reflexivity.
Qed.

Lemma hcy5_p12_x_spure_supd_addr (PS: list (val * share * peer)) a P' :
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [|[[x s] w] PS IH]; simpl; auto.
  hcy5_p12_x_spure_dif; simpl; f_equal; auto.
Qed.

Lemma hcy5_p12_x_spure_supd_wf PS a P' : peers_wf PS -> peers_wf (supd PS a P').
Proof.
  unfold peers_wf. induction PS as [|[[x s] w] PS IH]; simpl; intros H; auto.
  inv H. hcy5_p12_x_spure_dif; constructor; auto.
Qed.

Lemma hcy5_p12_x_spure_F2_refl {X: Type} (Rel: X -> X -> Prop) l :
  (forall x, In x l -> Rel x x) -> Forall2 Rel l l.
Proof.
  induction l as [|x l IH]; intros H; constructor.
  - apply H; simpl; auto.
  - apply IH. intros y Hy. apply H; simpl; auto.
Qed.

Lemma hcy5_p12_x_spure_F2_supd (Rel: val * share * peer -> val * share * peer -> Prop) PS a P' :
  (forall x, In x PS -> Rel x x) ->
  (forall p sh P, In (p, sh, P) PS -> p = a -> Rel (p, sh, P) (p, sh, P')) ->
  Forall2 Rel PS (supd PS a P').
Proof.
  induction PS as [|[[p s] P] PS IH]; simpl; intros H1 H2; [constructor|].
  destruct (EqDec_val p a) as [->|n]; constructor.
  - apply H2; auto.
  - apply hcy5_p12_x_spure_F2_refl. intros x Hx. apply H1; auto.
  - apply H1; auto.
  - apply IH; auto.
Qed.

Lemma hcy5_p12_x_spure_cmp_F2 own T PS PS' :
  Forall2 (fun x x' => match x, x' with (_, _, P0), (p, _, P) =>
             (In (hs_addr p) (saddrs (t_D T)) /\
              Forall (vp_ok own) (hs_ptrs (hs_snap_cur T (peer_addr4 x) P0) (hs_snap_cur T p P) ++ pr_ptrs P0 P))
           end) PS PS' ->
  hn4_cmp_ok own T (hcy5_p12_x_sns T PS) (hcy5_p12_x_prs PS) PS'.
Proof.
  intros H; induction H as [|x x' PS PS' Hx _ IH]; [simpl; auto|].
  destruct x as [[p0 s0] P0], x' as [[p s] P]. simpl. split; [exact Hx | exact IH].
Qed.

Lemma hcy5_p12_x_spure_same T a PS PS' :
  Forall2 (fun x x' => x' = x \/ peer_addr4 x' = a) PS PS' ->
  hnodes_same4 T a (hcy5_p12_x_sns T PS) (hcy5_p12_x_rs PS) (hcy5_p12_x_prs PS) PS' = true.
Proof.
  intros H; induction H as [|x x' PS PS' Hx _ IH]; [reflexivity|].
  destruct x' as [[p s] P]. destruct x as [[p0 s0] P0]. unfold hcy5_p12_x_sns, hcy5_p12_x_rs, hcy5_p12_x_prs in *.
  cbn [map hnodes_same4]. rewrite IH, andb_true_r. destruct Hx as [Hx|Ha].
  - inv Hx. destruct (eq_dec p0 a); auto.
    rewrite hcy5_p12_x_spure_snap_refl, Int.eq_true, hcy5_p12_x_spure_pr_refl. reflexivity.
  - simpl in Ha. subst. rewrite if_true; auto.
Qed.

(* the public-key chain: every pknext is NULL or a peer of the list *)
Lemma hcy5_p12_x_spure_chain_hd h PS : pk_chain h PS -> h = nullval \/ In h (map peer_addr4 PS).
Proof.
  destruct PS as [|[[p s] P] PS]; simpl; intros H; [auto|]. destruct H as [-> _]. auto.
Qed.

Lemma hcy5_p12_x_spure_chain h PS : pk_chain h PS ->
  Forall (fun x => match x with (_, _, P) => vp_ok (map peer_addr4 PS) (p_pknext P) end) PS.
Proof.
  revert h; induction PS as [|[[p s] P] PS IH]; simpl; intros h H; [constructor|].
  destruct H as [_ H]. constructor.
  - destruct (hcy5_p12_x_spure_chain_hd _ _ H) as [E|E]; [left; exact E | right; simpl; auto].
  - eapply Forall_impl; [|exact (IH _ H)]. intros [[q t] Q] Hq. destruct Hq as [Hq|Hq]; [left; auto | right; simpl; auto].
Qed.

Lemma hcy5_p12_x_spure_succ_in L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; auto.
  hcy5_p12_x_spure_dif.
  - destruct L; simpl; auto.
  - destruct IH; auto.
Qed.

Lemma hcy5_p12_x_spure_kaddrs T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. reflexivity. Qed.

(* sfind *)
Lemma hcy5_p12_x_spure_sfind_In {A: Type} (l: list (val * share * A)) a sh v :
  sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a) as [->|n]; [inv H; auto | right; auto].
Qed.

Lemma hcy5_p12_x_spure_sfind_nd {A: Type} (l: list (val * share * A)) a sh v :
  NoDup (saddrs l) -> In (a, sh, v) l -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros Hn H; [contradiction|].
  inv Hn. destruct (EqDec_val x a) as [->|n].
  - destruct H as [H|H]; [inv H; auto|].
    exfalso. match goal with Hx: ~ In a _ |- _ => apply Hx end.
    unfold saddrs. apply (in_map (fun '(x, _, _) => x)) in H. exact H.
  - destruct H as [H|H]; [inv H; congruence | auto].
Qed.

Lemma hcy5_p12_x_spure_entry PS KE T p :
  hcy5_T_ok PS KE T -> NoDup (saddrs (t_D T)) -> In p (map peer_addr4 PS) ->
  e_peer (t_entry_d T (hs_addr p)) = p /\ In (hs_addr p) (saddrs (t_D T)).
Proof.
  intros ((own & ix & HD & _) & _) Hn Hp.
  assert (Hin: In (hcy5_hent ix p) (t_D T)).
  { rewrite HD. unfold hcy5_pool. apply in_or_app. right. apply in_map. exact Hp. }
  unfold hcy5_hent in Hin. split.
  - unfold t_entry_d, t_entry. rewrite (hcy5_p12_x_spure_sfind_nd _ _ _ _ Hn Hin). reflexivity.
  - unfold saddrs. apply (in_map (fun '(x, _, _) => x)) in Hin. exact Hin.
Qed.

(* the consumption's result *)
Lemma hcy5_p12_x_spure_res xaead_dec T PS M now a P' :
  hcy5_res xaead_dec T PS M now = Some (a, P') ->
  exists sh P c, sfind PS a = Some (sh, P) /\ P' = p_set_cookie P c.
Proof.
  unfold hcy5_res, message_consume_model. intros H.
  destruct (t_lookup _ _ _) as [[x E]|]; [|discriminate].
  destruct (sfind PS (e_peer E)) as [[sh P]|] eqn:Hs; [|discriminate].
  destruct (negb _); [discriminate|].
  destruct (xaead_dec _ _ _ _); [|discriminate].
  inv H. eauto.
Qed.

(* the target cnode *)
Lemma hcy5_p12_x_spure_cfind NS CL a : hcy5_cfind NS CL a <> nullval ->
  exists nd o, In (hcy5_cfind NS CL a, nd, o) CL /\ hcy5_nodepeer NS nd = a.
Proof.
  induction CL as [| [[c nd] o] CL IH]; simpl; intros H; [congruence|].
  destruct (EqDec_val (hcy5_nodepeer NS nd) a) as [E|E].
  - exists nd, o. auto.
  - destruct (IH H) as (nd' & o' & H1 & H2). exists nd', o'. auto.
Qed.

Lemma hcy5_p12_x_spure_nodepeer NS nd : In nd (map hn_addr NS) ->
  exists N0, In N0 NS /\ hn_addr N0 = nd /\ hcy5_nodepeer NS nd = hn_p N0.
Proof.
  intros Hin. unfold hcy5_nodepeer.
  destruct (find _ NS) as [N0|] eqn:Hf.
  - apply find_some in Hf. destruct Hf as [H1 H2].
    destruct (eq_dec (hn_addr N0) nd); [|discriminate]. eauto.
  - exfalso. apply in_map_iff in Hin. destruct Hin as (N & HN & HinN).
    pose proof (find_none _ _ Hf N HinN) as Hx. cbv beta in Hx.
    revert Hx. match goal with |- context [if ?d then _ else _] => destruct d end; [discriminate | congruence].
Qed.

(* the node of the peer at a *)
Lemma hcy5_p12_x_spure_pick T NS PS N0 a sh P :
  map hn_p NS = map peer_addr4 PS -> NoDup (map peer_addr4 PS) ->
  In (a, sh, P) PS -> In N0 NS -> hn_p N0 = a ->
  exists NS1 NS2, hnodes_snapped4 T NS PS = NS1 ++ hn_snapshot4 T N0 (a, sh, P) :: NS2.
Proof.
  revert PS; induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hm Hnd HinP HinN Ha;
    simpl in Hm; try discriminate; try contradiction.
  injection Hm as H0 H1. rewrite hcy5_p12_x_spure_snapped_cons.
  destruct x as [[p s] Q]. simpl in H0. apply NoDup_cons_iff in Hnd. destruct Hnd as [H2 H3].
  destruct (EqDec_val (hn_p N) a) as [E|E].
  - assert (Hx: (p, s, Q) = (a, sh, P)).
    { destruct HinP as [HinP|HinP]; [exact HinP|].
      exfalso. apply (in_map peer_addr4) in HinP. simpl in HinP. apply H2. rewrite <- H0, E. exact HinP. }
    assert (HN: N = N0).
    { destruct HinN as [HinN|HinN]; [exact HinN|].
      exfalso. apply (in_map hn_p) in HinN. rewrite H1, Ha in HinN. apply H2. rewrite <- H0, E. exact HinN. }
    rewrite Hx, HN. exists [], (hnodes_snapped4 T NS PS). reflexivity.
  - assert (HinN': In N0 NS) by (destruct HinN as [HinN|HinN]; [subst N0; congruence | exact HinN]).
    assert (HinP': In (a, sh, P) PS) by (destruct HinP as [HinP|HinP]; [injection HinP as -> _ _; congruence | exact HinP]).
    destruct (IH PS H1 H3 HinP' HinN' Ha) as (NS1 & NS2 & E1).
    exists (hn_snapshot4 T N (p, s, Q) :: NS1), NS2. rewrite E1. reflexivity.
Qed.

(* the peers around a *)
Lemma hcy5_p12_x_spure_split (PS: list (val * share * peer)) a sh P P' :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  exists PS1 PS2, PS = PS1 ++ (a, sh, P) :: PS2 /\ supd PS a P' = PS1 ++ (a, sh, P') :: PS2.
Proof.
  intros Hnd Hin. destruct (in_split _ _ Hin) as (PS1 & PS2 & E). exists PS1, PS2. split; [exact E|].
  subst PS. rewrite map_app in Hnd. cbn [map peer_addr4] in Hnd.
  apply NoDup_remove_2 in Hnd. clear Hin.
  induction PS1 as [|[[x s] w] PS1 IH]; simpl.
  - rewrite if_true by reflexivity. reflexivity.
  - simpl in Hnd. rewrite if_false by (intros ->; apply Hnd; left; reflexivity).
    f_equal. apply IH. intros Hx. apply Hnd. right. exact Hx.
Qed.

Lemma hcy5_p12_x_spure_uniq (PS: list (val * share * peer)) a s1 Q1 s2 Q2 :
  NoDup (map peer_addr4 PS) -> In (a, s1, Q1) PS -> In (a, s2, Q2) PS -> s1 = s2 /\ Q1 = Q2.
Proof.
  induction PS as [|[[x s] w] PS IH]; simpl; intros Hn H1 H2; [contradiction|].
  apply NoDup_cons_iff in Hn. destruct Hn as [Hx Hn].
  destruct H1 as [H1|H1], H2 as [H2|H2].
  - inv H1; inv H2; auto.
  - inv H1. exfalso. apply Hx. apply (in_map peer_addr4) in H2. exact H2.
  - inv H2. exfalso. apply Hx. apply (in_map peer_addr4) in H1. exact H1.
  - auto.
Qed.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the objects lent to the comparisons: A's device (p_device, hs_sid) and the kents (keypair slots) *)
Definition hcy5_p12_x_VO (R: hcy5_run) (L: hcy5_loc) (T: tstate) (KE: list kent4) : list vobj :=
  [VDev Tsh (l_wa L) (hcy5_DA x25519 R L); VKents (hcy5_khead KE) (map (kent_snapped T) KE)].

(* common4 v4.1: VKents lends no address (a kent's address is its entry, a pool item of the table) *)
Lemma hcy5_p12_x_spure_VO_addrs R L T KE :
  vobjs_addrs (hcy5_p12_x_VO R L T KE) = [l_wa L; id_addr (l_wa L); cc_addr (l_wa L)].
Proof. unfold hcy5_p12_x_VO, vobjs_addrs. simpl. reflexivity. Qed.

Lemma hcy5_p12_x_spure_kpool PS KE T k :
  hcy5_T_ok PS KE T -> In k (map ke_addr KE) -> In k (saddrs (t_D T)).
Proof.
  intros ((own & ix & HD & _) & _) Hk. rewrite HD. unfold hcy5_pool, saddrs. rewrite map_app, in_app_iff. left.
  rewrite map_map. erewrite map_ext; [rewrite map_id; exact Hk | intros; reflexivity].
Qed.

Lemma hcy5_p12_x_spure_ok R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2 :
  hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2 ->
  itable_wf T ->
  hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2) <> nullval ->
  exists nd o N NS1 NS2 a P P' PS1 PS2,
    (* the target cnode and the node it points to *)
    In (hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2), nd, o) CL /\
    hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = nd /\ hn_p N = a /\
    hn_snap N = hsnap_val (hs_snap_cur T a P) /\ hn_refs N = Vint (p_refs P) /\ hn_rest N = prsnap_val P /\
    (* the peers after the consumption: a's peer P became P', only its cookie changed *)
    peers_after PS (hcy5_res xaead_dec T PS CM' now2) = PS1 ++ (a, Ews, P') :: PS2 /\
    p_refs P' = p_refs P /\ hs_snap_cur T a P' = hs_snap_cur T a P /\
    snap_eqb (hs_snap_cur T a P) (hs_snap_cur T a P') = true /\ pr_eqb_nc P P' = true /\
    (* hnodes_same_except(peers, a) *)
    Forall vobj_ok (hcy5_p12_x_VO R L T KE) /\
    hnodes_peers4 (hnodes_snapped4 T NS PS) (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) /\
    peers_wf (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) /\
    Zlength (hcy5_p12_x_sns T PS) = Zlength (hnodes_snapped4 T NS PS) /\
    Zlength (hcy5_p12_x_rs PS) = Zlength (hnodes_snapped4 T NS PS) /\
    Zlength (hcy5_p12_x_prs PS) = Zlength (hnodes_snapped4 T NS PS) /\
    map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hcy5_p12_x_sns T PS) /\
    map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hcy5_p12_x_rs PS) /\
    map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hcy5_p12_x_prs PS) /\
    hn4_cmp_ok (map peer_addr4 (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) ++ saddrs (t_D T) ++
                vobjs_addrs (hcy5_p12_x_VO R L T KE)) T
      (hcy5_p12_x_sns T PS) (hcy5_p12_x_prs PS) (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) /\
    (a = nullval \/ In a (map peer_addr4 (peers_after PS (hcy5_res xaead_dec T PS CM' now2)))) /\
    hnodes_same4 T a (hcy5_p12_x_sns T PS) (hcy5_p12_x_rs PS) (hcy5_p12_x_prs PS)
      (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) = true /\
    (* hs_same(&N.snap, &a->handshake), whole peer, VO lent *)
    In (hs_addr a) (saddrs (t_D T)) /\
    Forall (vp_ok (hs_own a T (hcy5_p12_x_VO R L T KE))) (hs_ptrs (hs_snap_cur T a P) (hs_snap_cur T a P')) /\
    (* pr_same_but_cookie(&N.rest, a), VO and the other peers lent *)
    vobj_ok (VPeers (PS1 ++ PS2)) /\
    Forall (vp_ok (a :: vobjs_addrs (hcy5_p12_x_VO R L T KE ++ [VPeers (PS1 ++ PS2); VItab Tsh (l_ita L) T])))
      (pr_ptrs P P').
Proof.
  intros Hinv Hw Ht.
  destruct Hinv as (_ & Hl & _ & HT & Hcl & _).
  destruct Hl as (Hpok & Hpeers & HndP & HndN & Hch).
  destruct Hw as (_ & Hincl & HndD & _).
  destruct (hcy5_res xaead_dec T PS CM' now2) as [[a P']|] eqn:Hres; [| exfalso; apply Ht; reflexivity].
  destruct (hcy5_p12_x_spure_res _ _ _ _ _ _ _ Hres) as (sh & P & c & Hsf & ->).
  apply hcy5_p12_x_spure_sfind_In in Hsf. rename Hsf into HinP.
  pose proof (proj1 (Forall_forall _ _) Hpok _ HinP) as Hk. unfold hcy5_pok in Hk.
  destruct Hk as (-> & Hdev & Hsid & _ & _ & _).
  cbn [hcy5_tgt peers_after] in *.
  destruct (hcy5_p12_x_spure_cfind _ _ _ Ht) as (nd & o & Hc & Hnp).
  assert (Hnd: In nd (map hn_addr NS)).
  { destruct Hcl as [Hcl _]. apply in_rev. rewrite <- Hcl.
    apply (in_map (fun x => snd (fst x))) in Hc. exact Hc. }
  destruct (hcy5_p12_x_spure_nodepeer _ _ Hnd) as (N0 & HinN0 & HaN0 & HpN0).
  rewrite HpN0 in Hnp.
  destruct (hcy5_p12_x_spure_pick T NS PS N0 a Ews P Hpeers HndP HinP HinN0 Hnp) as (NS1 & NS2 & ENS).
  destruct (hcy5_p12_x_spure_split PS a Ews P (p_set_cookie P c) HndP HinP) as (PS1 & PS2 & EPS & ESU).
  set (P' := p_set_cookie P c) in *.
  pose proof (hcy5_p12_x_spure_peers_len _ _ Hpeers) as Hlen.
  set (PS' := supd PS a P') in *.
  destruct (hcy5_p12_x_spure_snapped_maps T NS PS Hlen) as (H0 & H1 & H2 & H3 & H4).
  assert (HinA: In a (map peer_addr4 PS)) by (apply (in_map peer_addr4) in HinP; exact HinP).
  assert (Hwf: peers_wf PS).
  { unfold peers_wf. eapply Forall_impl; [|exact Hpok]. intros [[p s] Y] Hx. destruct Hx as [-> _]. auto. }
  assert (HVO := hcy5_p12_x_spure_VO_addrs R L T KE).
  assert (Hown: forall v, In v (map peer_addr4 PS) \/ In v (saddrs (t_D T)) \/
                          In v [l_wa L; id_addr (l_wa L); cc_addr (l_wa L)] \/ In v (map ke_addr KE) ->
                vp_ok (map peer_addr4 PS' ++ saddrs (t_D T) ++ vobjs_addrs (hcy5_p12_x_VO R L T KE)) v).
  { intros v Hv. right. unfold PS'. rewrite hcy5_p12_x_spure_supd_addr, HVO.
    assert (Hk := hcy5_p12_x_spure_kpool PS KE T v HT).
    rewrite !in_app_iff. tauto. }
  assert (Hchain := hcy5_p12_x_spure_chain _ _ Hch).
  set (own := map peer_addr4 PS' ++ saddrs (t_D T) ++ vobjs_addrs (hcy5_p12_x_VO R L T KE)) in *.
  assert (Hq: forall p sh Y, In (p, sh, Y) PS ->
            Forall (vp_ok own) [p_device Y; p_cur Y; p_prev Y; p_next Y; p_pknext Y; hs_sid (p_hs Y)]).
  { intros p sh0 Y Hin.
    pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hk. unfold hcy5_pok in Hk.
    destruct Hk as (_ & Hdev' & Hsid' & _ & _ & Hs).
    pose proof (proj1 (Forall_forall _ _) Hchain _ Hin) as Hc'. simpl in Hc'.
    rewrite Forall_forall in Hs.
    clearbody own.
    apply Forall_forall; intros v Hv; simpl in Hv.
    repeat (destruct Hv as [<-|Hv]); try contradiction.
    - rewrite Hdev'. apply Hown. right; right; left; simpl; auto.
    - destruct (Hs (p_cur Y)) as [E|E]; [simpl; auto | left; exact E | apply Hown; tauto].
    - destruct (Hs (p_prev Y)) as [E|E]; [simpl; auto | left; exact E | apply Hown; tauto].
    - destruct (Hs (p_next Y)) as [E|E]; [simpl; auto | left; exact E | apply Hown; tauto].
    - destruct Hc' as [E|E]; [left; exact E | apply Hown; tauto].
    - rewrite Hsid'. apply Hown. right; right; left; simpl; auto. }
  assert (Hpt: forall (p: val) (sh: share) (Y Y': peer), In (p, sh, Y) PS ->
            p_device Y' = p_device Y -> p_cur Y' = p_cur Y -> p_prev Y' = p_prev Y -> p_next Y' = p_next Y ->
            p_pknext Y' = p_pknext Y -> hs_sid (p_hs Y') = hs_sid (p_hs Y) ->
            In (hs_addr p) (saddrs (t_D T)) /\
            Forall (vp_ok own) (hs_ptrs (hs_snap_cur T p Y) (hs_snap_cur T p Y') ++ pr_ptrs Y Y')).
  { intros p sh0 Y Y' Hin E1 E2 E3 E4 E5 E6.
    assert (Hpa: In p (map peer_addr4 PS)) by (apply (in_map peer_addr4) in Hin; exact Hin).
    destruct (hcy5_p12_x_spure_entry PS KE T p HT HndD Hpa) as [He Hin_a].
    split; [exact Hin_a|].
    unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of, pr_ptrs. cbn [sn_next sn_entry sn_hs app].
    rewrite E1, E2, E3, E4, E5, E6, He.
    assert (Hsucc: vp_ok own (succ_in (t_L T) (hs_addr p))).
    { destruct (hcy5_p12_x_spure_succ_in (t_L T) (hs_addr p)) as [E|E]; [left; exact E|].
      apply Hown. right; left. apply Hincl, E. }
    assert (Hpo: vp_ok own p) by (apply Hown; tauto).
    pose proof (Hq _ _ _ Hin) as F1.
    clearbody own.
    apply Forall_forall. intros v Hv. simpl in Hv.
    rewrite Forall_forall in F1.
    repeat (destruct Hv as [<-|Hv]); try contradiction;
      first [exact Hsucc | exact Hpo | apply F1; simpl; tauto]. }
  pose proof (hcy5_p12_x_spure_entry PS KE T a HT HndD HinA) as [Hea Hina].
  exists nd, o, (hn_snapshot4 T N0 (a, Ews, P)), NS1, NS2, a, P, P', PS1, PS2.
  split; [exact Hc|].
  split; [exact ENS|].
  split; [exact HaN0|].
  split; [exact Hnp|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact ESU|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [apply hcy5_p12_x_spure_snap_refl|].
  split; [apply hcy5_p12_x_spure_pr_nc|].
  split.
  { unfold hcy5_p12_x_VO. repeat constructor; simpl; auto. }
  split; [unfold hnodes_peers4, PS'; rewrite H0, hcy5_p12_x_spure_supd_addr; exact Hpeers|].
  split; [apply hcy5_p12_x_spure_supd_wf; auto|].
  split; [unfold hcy5_p12_x_sns; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [unfold hcy5_p12_x_rs; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [unfold hcy5_p12_x_prs; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split.
  { apply hcy5_p12_x_spure_cmp_F2. unfold PS'. apply hcy5_p12_x_spure_F2_supd.
    - intros [[p sh0] Y] Hin. apply (Hpt p sh0 Y Y); auto.
    - intros p sh0 Y Hin ->.
      destruct (hcy5_p12_x_spure_uniq PS a sh0 Y Ews P HndP Hin HinP) as [_ ->].
      apply (Hpt a sh0 P P'); auto. }
  split; [right; unfold PS'; rewrite hcy5_p12_x_spure_supd_addr; exact HinA|].
  split.
  { apply hcy5_p12_x_spure_same. unfold PS'. apply hcy5_p12_x_spure_F2_supd; [intros; left; auto | intros; right; simpl; auto]. }
  split; [exact Hina|].
  split.
  { change (hs_snap_cur T a P') with (hs_snap_cur T a P).
    unfold hs_own, hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of. cbn [sn_next sn_entry sn_hs].
    rewrite Hea, Hsid, HVO. clearbody own PS'.
    apply Forall_forall; intros v Hv; simpl in Hv.
    repeat (destruct Hv as [<-|Hv]); try contradiction;
      first [ (destruct (hcy5_p12_x_spure_succ_in (t_L T) (hs_addr a)) as [E|E];
                 [left; exact E | right; right; apply in_or_app; left; apply Hincl, E])
            | (right; left; reflexivity)
            | (right; right; apply in_or_app; right; simpl; auto) ]. }
  assert (HinPS: forall x, In x (PS1 ++ PS2) -> In x PS).
  { intros x Hx. rewrite EPS. apply in_app_iff in Hx. apply in_or_app.
    destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]. }
  split.
  { simpl. apply Forall_forall. intros [[p s] Y] Hin.
    pose proof (proj1 (Forall_forall _ _) Hwf _ (HinPS _ Hin)) as Hs. simpl in Hs.
    apply writable_readable_share; exact Hs. }
  unfold vobjs_addrs at 1. rewrite map_app, concat_app.
  change (concat (map vobj_addrs (hcy5_p12_x_VO R L T KE))) with (vobjs_addrs (hcy5_p12_x_VO R L T KE)).
  rewrite HVO. cbn [map concat vobj_addrs]. rewrite app_nil_r.
  assert (Hown3: forall v, v = a \/ In v [l_wa L; id_addr (l_wa L); cc_addr (l_wa L)] \/ In v (map ke_addr KE) \/
                          In v (map peer_addr4 PS) ->
                vp_ok (a :: [l_wa L; id_addr (l_wa L); cc_addr (l_wa L)] ++
                       map peer_addr4 (PS1 ++ PS2) ++ (l_ita L :: saddrs (t_D T))) v).
  { intros v Hv. right. assert (Hk := hcy5_p12_x_spure_kpool PS KE T v HT).
    rewrite EPS in Hv. rewrite map_app in *. cbn [map peer_addr4] in Hv.
    rewrite !in_app_iff in *. destruct Hv as [->|Hv]; [left; reflexivity|].
    simpl in Hv |- *. rewrite ?in_app_iff in *. simpl. tauto. }
  pose proof (proj1 (Forall_forall _ _) Hpok _ HinP) as Hk. unfold hcy5_pok in Hk.
  destruct Hk as (_ & _ & _ & _ & _ & Hs). rewrite Forall_forall in Hs.
  pose proof (proj1 (Forall_forall _ _) Hchain _ HinP) as Hc'. simpl in Hc'.
  unfold pr_ptrs. unfold P', p_set_cookie. cbn [p_device p_cur p_prev p_next p_pknext].
  clearbody own PS'.
  apply Forall_forall; intros v Hv; simpl in Hv.
  repeat (destruct Hv as [<-|Hv]); try contradiction.
  all: first [ (rewrite Hdev; apply Hown3; right; left; simpl; auto)
             | (destruct Hc' as [E|E]; [left; exact E | apply Hown3; tauto])
             | (match goal with |- vp_ok _ ?k => destruct (Hs k) as [E|E];
                  [simpl; auto | left; exact E | apply Hown3; tauto] end) ].
Qed.

End Pure.
