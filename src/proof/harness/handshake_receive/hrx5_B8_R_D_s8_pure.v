(* law handshake_receive, B8 R D part S8: pure facts for CHECK(pr_same(&target->rest, target->p)).
   Copied from B8 I3, prefix hrx5_B8RDs8_. *)
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

Ltac hrx5_B8RDs8_dif := match goal with |- context [if ?d then _ else _] => destruct d end.

Lemma hrx5_B8RDs8_bytes_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hrx5_B8RDs8_veqb_refl x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hrx5_B8RDs8_snap_refl s : snap_eqb s s = true.
Proof.
  destruct s as [[p ty ix] nx hb H]. unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hrx5_B8RDs8_bytes_refl.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hrx5_B8RDs8_pr_refl P : pr_eqb P P = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb.
  rewrite ?hrx5_B8RDs8_veqb_refl, ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hrx5_B8RDs8_bytes_refl.
  reflexivity.
Qed.

Lemma hrx5_B8RDs8_pr_nc P c : pr_eqb_nc P (p_set_cookie P c) = true.
Proof.
  unfold pr_eqb_nc, p_set_cookie; cbn [p_device p_dead p_cur p_prev p_next p_lsh p_id p_pknext].
  rewrite ?hrx5_B8RDs8_veqb_refl, ?Int64.eq_true, ?Bool.eqb_reflx. reflexivity.
Qed.

Lemma hrx5_B8RDs8_snapped_cons T N NS x PS :
  hnodes_snapped4 T (N :: NS) (x :: PS) = hn_snapshot4 T N x :: hnodes_snapped4 T NS PS.
Proof. reflexivity. Qed.

Lemma hrx5_B8RDs8_peers_len NS PS : hnodes_peers4 NS PS -> length NS = length PS.
Proof.
  intros H. unfold hnodes_peers4 in H.
  rewrite <- (map_length hn_p NS), H, map_length. reflexivity.
Qed.

Lemma hrx5_B8RDs8_supd_addr (PS: list (val * share * peer)) a P' :
  map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof.
  induction PS as [|[[x s] w] PS IH]; simpl; auto.
  hrx5_B8RDs8_dif; simpl; f_equal; auto.
Qed.

Lemma hrx5_B8RDs8_supd_wf PS a P' : peers_wf PS -> peers_wf (supd PS a P').
Proof.
  unfold peers_wf. induction PS as [|[[x s] w] PS IH]; simpl; intros H; auto.
  inv H. hrx5_B8RDs8_dif; constructor; auto.
Qed.

Lemma hrx5_B8RDs8_F2_refl {X: Type} (Rel: X -> X -> Prop) l :
  (forall x, In x l -> Rel x x) -> Forall2 Rel l l.
Proof.
  induction l as [|x l IH]; intros H; constructor.
  - apply H; simpl; auto.
  - apply IH. intros y Hy. apply H; simpl; auto.
Qed.

Lemma hrx5_B8RDs8_F2_supd (Rel: val * share * peer -> val * share * peer -> Prop) PS a P' :
  (forall x, In x PS -> Rel x x) ->
  (forall p sh P, In (p, sh, P) PS -> p = a -> Rel (p, sh, P) (p, sh, P')) ->
  Forall2 Rel PS (supd PS a P').
Proof.
  induction PS as [|[[p s] P] PS IH]; simpl; intros H1 H2; [constructor|].
  destruct (EqDec_val p a) as [->|n]; constructor.
  - apply H2; auto.
  - apply hrx5_B8RDs8_F2_refl. intros x Hx. apply H1; auto.
  - apply H1; auto.
  - apply IH; auto.
Qed.

(* the public-key chain: every pknext is NULL or a peer of the list *)
Lemma hrx5_B8RDs8_chain_hd h PS : pk_chain h PS -> h = nullval \/ In h (map peer_addr4 PS).
Proof.
  destruct PS as [|[[p s] P] PS]; simpl; intros H; [auto|]. destruct H as [-> _]. auto.
Qed.

Lemma hrx5_B8RDs8_chain h PS : pk_chain h PS ->
  Forall (fun x => match x with (_, _, P) => vp_ok (map peer_addr4 PS) (p_pknext P) end) PS.
Proof.
  revert h; induction PS as [|[[p s] P] PS IH]; simpl; intros h H; [constructor|].
  destruct H as [_ H]. constructor.
  - destruct (hrx5_B8RDs8_chain_hd _ _ H) as [E|E]; [left; exact E | right; simpl; auto].
  - eapply Forall_impl; [|exact (IH _ H)]. intros [[q t] Q] Hq. destruct Hq as [Hq|Hq]; [left; auto | right; simpl; auto].
Qed.

Lemma hrx5_B8RDs8_succ_in L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; auto.
  hrx5_B8RDs8_dif.
  - destruct L; simpl; auto.
  - destruct IH; auto.
Qed.

Lemma hrx5_B8RDs8_kaddrs T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. reflexivity. Qed.

(* sfind *)
Lemma hrx5_B8RDs8_sfind_In {A: Type} (l: list (val * share * A)) a sh v :
  sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a) as [->|n]; [inv H; auto | right; auto].
Qed.

Lemma hrx5_B8RDs8_sfind_nd {A: Type} (l: list (val * share * A)) a sh v :
  NoDup (saddrs l) -> In (a, sh, v) l -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros Hn H; [contradiction|].
  inv Hn. destruct (EqDec_val x a) as [->|n].
  - destruct H as [H|H]; [inv H; auto|].
    exfalso. match goal with Hx: ~ In a _ |- _ => apply Hx end.
    unfold saddrs. apply (in_map (fun '(x, _, _) => x)) in H. exact H.
  - destruct H as [H|H]; [inv H; congruence | auto].
Qed.

(* the consumption's result *)

(* the target cnode *)

(* the node of the peer at a *)
Lemma hrx5_B8RDs8_pick T NS PS N0 a sh P :
  map hn_p NS = map peer_addr4 PS -> NoDup (map peer_addr4 PS) ->
  In (a, sh, P) PS -> In N0 NS -> hn_p N0 = a ->
  exists NS1 NS2, hnodes_snapped4 T NS PS = NS1 ++ hn_snapshot4 T N0 (a, sh, P) :: NS2.
Proof.
  revert PS; induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hm Hnd HinP HinN Ha;
    simpl in Hm; try discriminate; try contradiction.
  injection Hm as H0 H1. rewrite hrx5_B8RDs8_snapped_cons.
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
Lemma hrx5_B8RDs8_split (PS: list (val * share * peer)) a sh P P' :
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

Lemma hrx5_B8RDs8_uniq (PS: list (val * share * peer)) a s1 Q1 s2 Q2 :
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

(* ---------------------------------------------------------------------- *)
(* handshake_receive specific                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RDs8_nfind NS a : hrx5_nfind NS a <> nullval ->
  exists N0, In N0 NS /\ hn_addr N0 = hrx5_nfind NS a /\ hn_p N0 = a.
Proof.
  induction NS as [|N NS IH]; simpl; intros H; [congruence|].
  destruct (EqDec_val (hn_p N) a) as [E|E].
  - exists N. auto.
  - destruct (IH H) as (N0 & H1 & H2 & H3). exists N0. auto.
Qed.

Lemma hrx5_B8RDs8_F2_in {X Y: Type} (Rel: X -> Y -> Prop) l1 l2 x :
  Forall2 Rel l1 l2 -> In x l1 -> exists y, In y l2 /\ Rel x y.
Proof.
  intros H; induction H as [|x1 y1 l1 l2 Hr _ IH]; intros Hin; [contradiction|].
  destruct Hin as [<-|Hin]; [exists y1; split; [left|]; auto|].
  destruct (IH Hin) as (y & Hy & Hr'). exists y. split; [right|]; auto.
Qed.

Lemma hrx5_B8RDs8_entry KA PS T p sh P :
  hrx5cr_pool KA PS T -> NoDup (saddrs (t_D T)) -> In (p, sh, P) PS ->
  e_peer (t_entry_d T (hs_addr p)) = p /\ In (hs_addr p) (saddrs (t_D T)).
Proof.
  intros [_ Hp] Hn Hin.
  destruct (hrx5_B8RDs8_F2_in _ _ _ _ Hp Hin) as ([[x s] E] & Hy & Hr).
  simpl in Hr. destruct Hr as (-> & -> & He & _).
  assert (HinD: In (hs_addr p, Ews, E) (t_D T)).
  { rewrite <- (firstn_skipn (length KA) (t_D T)). apply in_or_app. right. exact Hy. }
  split.
  - unfold t_entry_d, t_entry. rewrite (hrx5_B8RDs8_sfind_nd _ _ _ _ Hn HinD). exact He.
  - unfold saddrs. apply (in_map (fun '(x, _, _) => x)) in HinD. exact HinD.
Qed.

Lemma hrx5_B8RDs8_nfind_in NS a : In a (map hn_p NS) ->
  exists N0, In N0 NS /\ hn_addr N0 = hrx5_nfind NS a /\ hn_p N0 = a.
Proof.
  induction NS as [|N NS IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val (hn_p N) a) as [E|E].
  - exists N. auto.
  - destruct H as [H|H]; [contradiction|].
    destruct (IH H) as (N0 & H1 & H2 & H3). exists N0. auto.
Qed.

Lemma hrx5_B8RDs8_veqb_refl' x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

(* the node of a peer is unique *)
Lemma hrx5_B8RDs8_nfind_uniq NS N0 a : NoDup (map hn_p NS) -> In N0 NS -> hn_p N0 = a ->
  hrx5_nfind NS a = hn_addr N0.
Proof.
  induction NS as [|N NS IH]; simpl; intros Hn Hin Ha; [contradiction|].
  apply NoDup_cons_iff in Hn. destruct Hn as [Hx Hn].
  destruct (EqDec_val (hn_p N) a) as [E|E].
  - destruct Hin as [<-|Hin]; [reflexivity|].
    exfalso. apply Hx. rewrite E, <- Ha. apply in_map. exact Hin.
  - destruct Hin as [<-|Hin]; [congruence|]. auto.
Qed.

(* the peer at the end of branch R has P's rest *)
Lemma hrx5_B8RDs8_pr_eqb d P M ck h : pr_eqb P (hrx5_B8R_Pf d P M ck h) = true.
Proof.
  unfold hrx5_B8R_Pf, hrx5cr_new.
  destruct (hrx5_B8R_alloc d);
  unfold pr_eqb, pr_eqb_nc, cookie_eqb, p_set_hs, p_set_refs;
  destruct P; cbn - [veqb bytes_eqb Int64.eq];
  rewrite !hrx5_B8RDs8_veqb_refl', !hrx5_B8RDs8_bytes_refl, !Int64.eq_true, !eqb_reflx; reflexivity.
Qed.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.

(* the objects lent to pr_same: the device and the other peers *)
Definition hrx5_B8RDs8_VO (L: hrx5_loc) (D: device) (PS: list (val * share * peer)) : list vobj :=
  [VDev Tsh (l_wd L) D; VPeers PS].

Lemma hrx5_B8RDs8_pure R L NS PS KE T head nk a P P' j D :
  hrx5_inv x25519 R L NS PS KE T head nk -> 0 <= j < Zlength PS -> Znth j PS = (a, Ews, P) ->
  hn_p (Znth j NS) = a ->
  p_device P' = p_device P -> p_cur P' = p_cur P -> p_prev P' = p_prev P -> p_next P' = p_next P ->
  p_pknext P' = p_pknext P ->
  exists N NS1 NS2 PS1 PS2,
    hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hn_addr (Znth j NS) /\ hn_p N = a /\
    hn_rest N = prsnap_val P /\
    supd PS a P' = PS1 ++ (a, Ews, P') :: PS2 /\
    Forall vobj_ok (hrx5_B8RDs8_VO L D (PS1 ++ PS2)) /\
    Forall (vp_ok (a :: vobjs_addrs (hrx5_B8RDs8_VO L D (PS1 ++ PS2)))) (pr_ptrs P P').
Proof.
  intros Hinv Hj HZ HjN E1 E2 E3 E4 E5.
  destruct Hinv as (Hpok & Hwf & HndP & Hch & Hpeers & _ & _).
  assert (HinP: In (a, Ews, P) PS) by (rewrite <- HZ; apply Znth_In; exact Hj).
  pose proof (proj1 (Forall_forall _ _) Hpok _ HinP) as Hk. unfold hrx5_pok in Hk.
  destruct Hk as (_ & Hdev & _ & _ & _ & _ & _ & _ & Hcur & Hprev & Hnext).
  assert (HlenN: Zlength NS = Zlength PS).
  { rewrite !Zlength_correct, (hrx5_B8RDs8_peers_len _ _ Hpeers). reflexivity. }
  assert (HinN0: In (Znth j NS) NS) by (apply Znth_In; rewrite HlenN; exact Hj).
  assert (HndN: NoDup (map hn_p NS)) by (unfold hnodes_peers4 in Hpeers; rewrite Hpeers; exact HndP).
  destruct (hrx5_B8RDs8_pick T NS PS (Znth j NS) a Ews P Hpeers HndP HinP HinN0 HjN) as (NS1 & NS2 & ENS).
  destruct (hrx5_B8RDs8_split PS a Ews P P' HndP HinP) as (PS1 & PS2 & EPS & ESU).
  exists (hn_snapshot4 T (Znth j NS) (a, Ews, P)), NS1, NS2, PS1, PS2.
  split; [exact ENS|].
  split; [reflexivity|].
  split; [exact HjN|].
  split; [reflexivity|].
  split; [exact ESU|].
  assert (HinPS: forall x, In x (PS1 ++ PS2) -> In x PS).
  { intros x Hx. rewrite EPS. apply in_app_iff in Hx. apply in_or_app.
    destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]. }
  split.
  { unfold hrx5_B8RDs8_VO. constructor; [simpl; auto|]. constructor; [|constructor].
    simpl. apply Forall_forall. intros [[p s] Y] Hin.
    pose proof (proj1 (Forall_forall _ _) Hwf _ (HinPS _ Hin)) as Hs. simpl in Hs.
    apply writable_readable_share; exact Hs. }
  unfold hrx5_B8RDs8_VO, vobjs_addrs. cbn [map concat vobj_addrs]. rewrite app_nil_r.
  assert (Hown3: forall v, v = a \/ v = l_wd L \/ In v (map peer_addr4 PS) ->
                vp_ok (a :: ([l_wd L; id_addr (l_wd L); cc_addr (l_wd L)] ++ map peer_addr4 (PS1 ++ PS2))) v).
  { intros v Hv. right. rewrite EPS in Hv. rewrite map_app in *. cbn [map peer_addr4] in Hv.
    rewrite !in_app_iff in *. destruct Hv as [->|[->|Hv]]; [left; reflexivity| right; left; simpl; auto|].
    simpl in Hv |- *. rewrite ?in_app_iff in *. tauto. }
  assert (Hchain := hrx5_B8RDs8_chain _ _ Hch).
  pose proof (proj1 (Forall_forall _ _) Hchain _ HinP) as Hc'. simpl in Hc'.
  unfold pr_ptrs. rewrite E1, E2, E3, E4, E5, Hdev, Hcur, Hprev, Hnext.
  apply Forall_forall; intros v Hv; simpl in Hv.
  repeat (destruct Hv as [<-|Hv]); try contradiction.
  all: first [ (left; reflexivity)
             | solve [apply Hown3; right; left; reflexivity]
             | (destruct Hc' as [E|E]; [left; exact E | apply Hown3; tauto]) ].
Qed.

End Pure.
