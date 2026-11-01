(* law handshake_receive, B4 segment R: pure facts of the response model block (table walk,
   pool handshake entries, node loop).  Rename-port of consume_response_any's hcr5_q3_pure.v. *)
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
#[local] Existing Instance W_handshake_receive.
#[local] Existing Instance W_handshake_receive.
(* the node the harness's loop `for (it = peers; it; it = it->next) if (&it->p->handshake.entry == e) p = it;`
   leaves in p: the LAST node of the list whose peer's handshake entry is at e, or NULL *)
Definition hrx5_B4_R_lm (l: list hnode4) (e: val) : val :=
  fold_left (fun acc N => if eq_dec (hs_addr (hn_p N)) e then hn_addr N else acc) l nullval.

Definition hrx5_B4_R_pure_stmt : Prop :=
  (* 1: the table's lookup finds an entry of the list, with its pool contents *)
  (forall T L idx a E, t_find_index T L idx = Some (a, E) -> In a L /\ t_entry T a = Some E) /\
  (* 2: a handshake entry of the pool is a peer's handshake entry *)
  (forall KA PS T a E, hrx5cr_pool KA PS T -> NoDup (saddrs (t_D T)) -> t_entry T a = Some E ->
     e_type E = IDX_HANDSHAKE ->
     a = hs_addr (e_peer E) /\ exists sh P, sfind PS (e_peer E) = Some (sh, P) /\ In (e_peer E, sh, P) PS) /\
  (* 3: every peer's handshake entry is in the pool *)
  (forall KA PS T p sh P, hrx5cr_pool KA PS T -> In (p, sh, P) PS -> In (hs_addr p) (saddrs (t_D T))) /\
  (* 4: the node loop's result is the harness model's node *)
  (forall T NS PS p0, hnodes_peers4 NS PS -> NoDup (map peer_addr4 PS) -> isptr (hs_addr p0) ->
     hrx5_B4_R_lm (hnodes_snapped4 T NS PS) (hs_addr p0) = hrx5_nfind NS p0) /\
  (* 5: the node of a peer, with its snapshot (taken from the peers before the call) *)
  (forall T NS PS p0 sh P, hnodes_peers4 NS PS -> sfind PS p0 = Some (sh, P) ->
     exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hrx5_nfind NS p0 /\
       hn_p N = p0 /\ hn_snap N = hsnap_val (hs_snap_cur T p0 P) /\ In (p0, sh, P) PS) /\
  (* 6: the snapshot keeps the nodes' addresses and peers *)
  (forall T NS PS, hnodes_peers4 NS PS ->
     map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS /\ map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS /\
     hrx5_head (hnodes_snapped4 T NS PS) = hrx5_head NS) /\
  (* 7: updating a peer keeps the addresses *)
  (forall (PS: list (val * share * peer)) a P', map peer_addr4 (supd PS a P') = map peer_addr4 PS).

Ltac hrx5_B4_Rp_desif := match goal with
  | |- context [if ?d then _ else _] => destruct d
  | H: context [if ?d then _ else _] |- _ => destruct d
  end.

Lemma hrx5_B4_Rp_sfind_In {A} (l: list (val * share * A)) a sh v : sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [|[[x s] w] l IH]; simpl; [discriminate|]. intros H.
  hrx5_B4_Rp_desif; [inversion H; subst; left; reflexivity | right; auto].
Qed.

Lemma hrx5_B4_Rp_In_sfind {A} (l: list (val * share * A)) a sh v : In (a, sh, v) l -> exists sh' v', sfind l a = Some (sh', v').
Proof.
  induction l as [|[[x s] w] l IH]; simpl; [tauto|]. intros H.
  hrx5_B4_Rp_desif; [eauto|]. destruct H as [H|H]; [inversion H; subst; congruence | auto].
Qed.

Lemma hrx5_B4_Rp_F2_In_r {X Y} (R: X -> Y -> Prop) l1 l2 y : Forall2 R l1 l2 -> In y l2 -> exists x, In x l1 /\ R x y.
Proof. induction 1; simpl; [tauto|]. intros [<-|H1]; [eauto|]. destruct (IHForall2 H1) as (x0 & ? & ?); eauto. Qed.

Lemma hrx5_B4_Rp_F2_In_l {X Y} (R: X -> Y -> Prop) l1 l2 x : Forall2 R l1 l2 -> In x l1 -> exists y, In y l2 /\ R x y.
Proof. induction 1; simpl; [tauto|]. intros [<-|H1]; [eauto|]. destruct (IHForall2 H1) as (y0 & ? & ?); eauto. Qed.

Lemma hrx5_B4_Rp_hs_addr_eq q p0 : isptr (hs_addr p0) -> hs_addr q = hs_addr p0 -> q = p0.
Proof.
  unfold hs_addr; destruct p0; simpl; try contradiction; intros _.
  destruct q; simpl; try discriminate. intros H.
  assert (H': Ptrofs.add i0 (Ptrofs.repr OFS_PEER_HANDSHAKE) = Ptrofs.add i (Ptrofs.repr OFS_PEER_HANDSHAKE)) by congruence.
  assert (b = b0) as -> by congruence.
  f_equal. rewrite <- (Ptrofs.add_zero i0), <- (Ptrofs.add_zero i).
  rewrite <- (Ptrofs.add_neg_zero (Ptrofs.repr OFS_PEER_HANDSHAKE)), <- !Ptrofs.add_assoc, H'. reflexivity.
Qed.

Lemma hrx5_B4_Rp_gmap (g: hnode4 -> val * share * peer -> hnode4) NS (PS: list (val * share * peer)) :
  (forall N x, hn_addr (g N x) = hn_addr N /\ hn_p (g N x) = hn_p N) -> length NS = length PS ->
  map hn_addr (map (fun '(N, x) => g N x) (combine NS PS)) = map hn_addr NS /\
  map hn_p (map (fun '(N, x) => g N x) (combine NS PS)) = map hn_p NS /\
  (forall a, hrx5_nfind (map (fun '(N, x) => g N x) (combine NS PS)) a = hrx5_nfind NS a) /\
  hrx5_head (map (fun '(N, x) => g N x) (combine NS PS)) = hrx5_head NS.
Proof.
  intros Hg. revert PS; induction NS as [|N NS IH]; intros [|x PS] HL; try discriminate; [simpl; auto|].
  destruct (IH PS ltac:(simpl in HL; lia)) as (A1 & A2 & A3 & A4). destruct (Hg N x) as [E1 E2].
  cbn [combine map hrx5_nfind hrx5_head]. rewrite A1, A2, E1, E2. repeat split; auto.
  intros a. rewrite A3. reflexivity.
Qed.

Lemma hrx5_B4_Rp_snapshot_keeps T N x : hn_addr (hn_snapshot4 T N x) = hn_addr N /\ hn_p (hn_snapshot4 T N x) = hn_p N.
Proof. destruct x as [[p s] P]. split; reflexivity. Qed.

Lemma hrx5_B4_Rp_snap_len T NS PS : hnodes_peers4 NS PS ->
  map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS /\ map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS /\
  (forall a, hrx5_nfind (hnodes_snapped4 T NS PS) a = hrx5_nfind NS a) /\
  hrx5_head (hnodes_snapped4 T NS PS) = hrx5_head NS.
Proof.
  intros H. apply (hrx5_B4_Rp_gmap (hn_snapshot4 T)); [apply hrx5_B4_Rp_snapshot_keeps|].
  unfold hnodes_peers4 in H. apply (f_equal (@length val)) in H. rewrite !map_length in H. exact H.
Qed.

Lemma hrx5_B4_Rp_lm_notin l e acc : (forall N, In N l -> hs_addr (hn_p N) <> e) ->
  fold_left (fun acc N => if eq_dec (hs_addr (hn_p N)) e then hn_addr N else acc) l acc = acc.
Proof.
  revert acc; induction l as [|N l IH]; intros acc H; simpl; auto.
  hrx5_B4_Rp_desif; [exfalso; eapply H; [left|]; eauto|]. apply IH; intros; apply H; right; auto.
Qed.

Lemma hrx5_B4_Rp_lm_nfind l p0 : NoDup (map hn_p l) -> isptr (hs_addr p0) -> hrx5_B4_R_lm l (hs_addr p0) = hrx5_nfind l p0.
Proof.
  unfold hrx5_B4_R_lm. induction l as [|N l IH]; intros ND HP; simpl; auto.
  inversion ND; subst. hrx5_B4_Rp_desif.
  - apply hrx5_B4_Rp_hs_addr_eq in e; auto. hrx5_B4_Rp_desif; [|congruence].
    apply hrx5_B4_Rp_lm_notin. intros N' HN' E'. apply hrx5_B4_Rp_hs_addr_eq in E'; auto.
    apply H1. rewrite e, <- E'. apply in_map; auto.
  - hrx5_B4_Rp_desif; [subst; congruence|]. auto.
Qed.

Lemma hrx5_B4_Rp_split_gen (g: hnode4 -> val * share * peer -> hnode4) (Pr: hnode4 -> Prop) NS PS p0 sh P :
  (forall N x, hn_addr (g N x) = hn_addr N /\ hn_p (g N x) = hn_p N) -> (forall N, Pr (g N (p0, sh, P))) ->
  map hn_p NS = map peer_addr4 PS -> sfind PS p0 = Some (sh, P) ->
  exists NS1 N NS2, map (fun '(N, x) => g N x) (combine NS PS) = NS1 ++ N :: NS2 /\ hn_addr N = hrx5_nfind NS p0 /\
    hn_p N = p0 /\ Pr N.
Proof.
  intros Hg HP. revert PS; induction NS as [|N NS IH]; intros [|[[x s] Q] PS] H HS;
    cbn [map combine sfind hrx5_nfind peer_addr4] in H, HS |- *; try discriminate.
  injection H as H1 H2. subst x. destruct (eq_dec (hn_p N) p0) as [e|ne].
  - injection HS as Hs HQ. subst s Q. rewrite e in *.
    exists [], (g N (p0, sh, P)), (map (fun '(N, x) => g N x) (combine NS PS)).
    destruct (Hg N (p0, sh, P)) as [E1 E2]. rewrite E1, E2, e. auto.
  - destruct (IH PS H2 HS) as (NS1 & N' & NS2 & A1 & A2 & A3 & A4).
    exists (g N (hn_p N, s, Q) :: NS1), N', NS2. rewrite A1. auto.
Qed.

Lemma hrx5_B4_Rp_split T NS PS p0 sh P : hnodes_peers4 NS PS -> sfind PS p0 = Some (sh, P) ->
  exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hrx5_nfind NS p0 /\
    hn_p N = p0 /\ hn_snap N = hsnap_val (hs_snap_cur T p0 P).
Proof.
  intros HN HS.
  apply (hrx5_B4_Rp_split_gen (hn_snapshot4 T) (fun N => hn_snap N = hsnap_val (hs_snap_cur T p0 P)) NS PS p0 sh P);
    auto using hrx5_B4_Rp_snapshot_keeps.
Qed.

Lemma hrx5_B4_Rp_supd_addrs (PS: list (val * share * peer)) a P' : map peer_addr4 (supd PS a P') = map peer_addr4 PS.
Proof. induction PS as [|[[x s] Q] PS IH]; simpl; auto. hrx5_B4_Rp_desif; simpl; f_equal; auto. Qed.

Lemma hrx5_B4_Rp_pool_in KA PS T a sh E : hrx5cr_pool KA PS T -> In (a, sh, E) (t_D T) -> e_type E = IDX_HANDSHAKE ->
  exists p s' P, In (p, s', P) PS /\ a = hs_addr p /\ e_peer E = p.
Proof.
  intros (H1 & H2) HI HT. rewrite <- (firstn_skipn (length KA) (t_D T)) in HI.
  apply in_app_or in HI as [HI|HI].
  - destruct (hrx5_B4_Rp_F2_In_r _ _ _ _ H1 HI) as (K & _ & (_ & _ & _ & HT')).
    rewrite HT in HT'. unfold IDX_HANDSHAKE, IDX_KEYPAIR in HT'. exfalso; apply repr_inj_unsigned in HT'; rep_lia.
  - destruct (hrx5_B4_Rp_F2_In_r _ _ _ _ H2 HI) as ([[p s'] P] & HP & (? & _ & ? & _)). exists p, s', P. auto.
Qed.

Lemma hrx5_B4_Rp_pool_hs KA PS T p sh P : hrx5cr_pool KA PS T -> In (p, sh, P) PS ->
  exists s' E, In (hs_addr p, s', E) (t_D T).
Proof.
  intros (H1 & H2) HI. destruct (hrx5_B4_Rp_F2_In_l _ _ _ _ H2 HI) as ([[a s'] E] & HA & (-> & _)).
  exists s', E. rewrite <- (firstn_skipn (length KA) (t_D T)). apply in_or_app; auto.
Qed.

Definition hrx5_B4_Rp_C1 : Prop :=
  forall T L idx a E, t_find_index T L idx = Some (a, E) -> In a L /\ t_entry T a = Some E.
Definition hrx5_B4_Rp_C2 : Prop :=
  forall KA PS T a E, hrx5cr_pool KA PS T -> NoDup (saddrs (t_D T)) -> t_entry T a = Some E ->
     e_type E = IDX_HANDSHAKE ->
     a = hs_addr (e_peer E) /\ exists sh P, sfind PS (e_peer E) = Some (sh, P) /\ In (e_peer E, sh, P) PS.
Definition hrx5_B4_Rp_C3 : Prop :=
  forall KA PS T p sh P, hrx5cr_pool KA PS T -> In (p, sh, P) PS -> In (hs_addr p) (saddrs (t_D T)).
Definition hrx5_B4_Rp_C4 : Prop :=
  forall T NS PS p0, hnodes_peers4 NS PS -> NoDup (map peer_addr4 PS) -> isptr (hs_addr p0) ->
     hrx5_B4_R_lm (hnodes_snapped4 T NS PS) (hs_addr p0) = hrx5_nfind NS p0.
Definition hrx5_B4_Rp_C5 : Prop :=
  forall T NS PS p0 sh P, hnodes_peers4 NS PS -> sfind PS p0 = Some (sh, P) ->
     exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hrx5_nfind NS p0 /\
       hn_p N = p0 /\ hn_snap N = hsnap_val (hs_snap_cur T p0 P) /\ In (p0, sh, P) PS.
Definition hrx5_B4_Rp_C6 : Prop :=
  forall T NS PS, hnodes_peers4 NS PS ->
     map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS /\ map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS /\
     hrx5_head (hnodes_snapped4 T NS PS) = hrx5_head NS.
Definition hrx5_B4_Rp_C7 : Prop :=
  forall (PS: list (val * share * peer)) a P', map peer_addr4 (supd PS a P') = map peer_addr4 PS.

Lemma hrx5_B4_Rp_c1 : hrx5_B4_Rp_C1.
Proof.
  intros T L idx a E. induction L as [|b L IH]; simpl; [discriminate|].
  destruct (t_entry T b) eqn:HB; [|intros H; destruct (IH H); auto].
  destruct (Int.eq (e_index e) idx); [intros H; inversion H; subst; auto|intros H; destruct (IH H); auto].
Qed.

Lemma hrx5_B4_Rp_c2 : hrx5_B4_Rp_C2.
Proof.
  intros KA PS T a E HP _ HE HT. unfold t_entry in HE. destruct (sfind (t_D T) a) as [[s E']|] eqn:HS; [|discriminate].
  inversion HE; subst. apply hrx5_B4_Rp_sfind_In in HS.
  destruct (hrx5_B4_Rp_pool_in _ _ _ _ _ _ HP HS HT) as (p & s' & P & HI & -> & ->). split; auto.
  destruct (hrx5_B4_Rp_In_sfind _ _ _ _ HI) as (sh' & P' & HF). exists sh', P'. split; auto. apply hrx5_B4_Rp_sfind_In; auto.
Qed.

Lemma hrx5_B4_Rp_c3 : hrx5_B4_Rp_C3.
Proof.
  intros KA PS T p sh P HP HI. destruct (hrx5_B4_Rp_pool_hs _ _ _ _ _ _ HP HI) as (s' & E & HD).
  unfold saddrs. change (hs_addr p) with ((fun '(x, _, _) => x) (hs_addr p, s', E)). apply in_map; auto.
Qed.

Lemma hrx5_B4_Rp_c4 : hrx5_B4_Rp_C4.
Proof.
  intros T NS PS p0 HN ND HP. destruct (hrx5_B4_Rp_snap_len T _ _ HN) as (_ & A2 & A3 & _).
  rewrite hrx5_B4_Rp_lm_nfind, A3; auto. rewrite A2. unfold hnodes_peers4 in HN. rewrite HN; auto.
Qed.

Lemma hrx5_B4_Rp_c5 : hrx5_B4_Rp_C5.
Proof.
  intros T NS PS p0 sh P HN HS. apply hrx5_B4_Rp_sfind_In in HS as HI.
  destruct (hrx5_B4_Rp_split T NS PS p0 sh P HN HS) as (NS1 & N & NS2 & ? & ? & ? & ?).
  exists NS1, N, NS2. auto.
Qed.

Lemma hrx5_B4_Rp_c6 : hrx5_B4_Rp_C6.
Proof. intros T NS PS HN. destruct (hrx5_B4_Rp_snap_len T _ _ HN) as (? & ? & _ & ?). auto. Qed.

Lemma hrx5_B4_Rp_c7 : hrx5_B4_Rp_C7.
Proof. exact hrx5_B4_Rp_supd_addrs. Qed.

Lemma hrx5_B4_R_pure_ok : hrx5_B4_R_pure_stmt.
Proof.
  exact (@conj hrx5_B4_Rp_C1 _ hrx5_B4_Rp_c1 (@conj hrx5_B4_Rp_C2 _ hrx5_B4_Rp_c2 (@conj hrx5_B4_Rp_C3 _ hrx5_B4_Rp_c3
    (@conj hrx5_B4_Rp_C4 _ hrx5_B4_Rp_c4 (@conj hrx5_B4_Rp_C5 _ hrx5_B4_Rp_c5 (@conj hrx5_B4_Rp_C6 hrx5_B4_Rp_C7 hrx5_B4_Rp_c6 hrx5_B4_Rp_c7)))))).
Qed.
