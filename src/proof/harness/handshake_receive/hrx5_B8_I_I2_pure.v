(* law handshake_receive, phase B8 branch I, segment I2: the pure
   facts the CHECK of I2 needs (port of consume_initiation_any's hci5_p8_A3_facts, the parts I2 uses, and of
   hrx5_B8_C_W_pure.v's pool lemmas): the accepted peer's node in the snapshotted list (its snapshot hs_snap_cur T a
   P), the peer in PS with share Ews, its handshake entry in T's pool (peer a), every pool share Ews. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_pure.

Local Open Scope Z_scope.

Lemma hrx5_B8I_I2_sfind : forall (PS: list (val * share * peer)) a sh P, NoDup (map peer_addr4 PS) ->
  In (a, sh, P) PS -> sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x sh0] w] PS IH]; simpl; intros a sh P Hnd Hin; [contradiction|].
  inv Hnd. destruct Hin as [Heq | Hin].
  - inv Heq. rewrite if_true by auto. reflexivity.
  - rewrite if_false; [eauto|]. intros ->. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hrx5_B8I_I2_split T : forall PS NS a sh P,
  map hn_p NS = map peer_addr4 PS -> NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ hn_snapshot4 T N (a, sh, P) :: NS2 /\
    hrx5_nfind NS a = hn_addr N /\ hn_p N = a.
Proof.
  induction PS as [|[[x sh0] Q] PS IH]; intros NS a sh P Hmap Hnd Hin; [contradiction|].
  destruct NS as [|N0 NS]; [discriminate|]. simpl in Hmap. injection Hmap as Hx Hmap. subst x.
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [H1 H2].
  change (hnodes_snapped4 T (N0 :: NS) ((hn_p N0, sh0, Q) :: PS)) with
    (hn_snapshot4 T N0 (hn_p N0, sh0, Q) :: hnodes_snapped4 T NS PS).
  destruct Hin as [Heq | Hin].
  - inv Heq. exists [], N0, (hnodes_snapped4 T NS PS).
    simpl. rewrite if_true by auto. auto.
  - destruct (IH NS a sh P Hmap H2 Hin) as (NS1 & N & NS2 & E & Ha & Hp).
    exists (hn_snapshot4 T N0 (hn_p N0, sh0, Q) :: NS1), N, NS2.
    split; [rewrite E; reflexivity|]. split; [| auto].
    simpl. rewrite if_false; auto. intros Hx. rewrite Hx in H1. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hrx5_B8I_I2_sfind_nodup: forall (l: list (val * share * entry)) a sh v,
  NoDup (saddrs l) -> In (a, sh, v) l -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros a sh v Hn H; [contradiction|].
  unfold saddrs in Hn; simpl in Hn; inv Hn.
  destruct (eq_dec x a) as [->|n]; [rewrite if_true by auto|rewrite if_false by auto].
  - destruct H as [H|H]; [inv H; reflexivity|].
    exfalso; apply H2. apply (in_map (fun '(x, _, _) => x) l (a, sh, v)) in H; exact H.
  - destruct H as [H|H]; [inv H; congruence|]. apply IH; auto.
Qed.

Lemma hrx5_B8I_I2_hs_in: forall D PS l, Forall2 hrx5cr_hs_ok PS l -> incl l D ->
  Forall (fun x => exists E, In (hs_addr (peer_addr4 x), Ews, E) D /\ e_peer E = peer_addr4 x) PS.
Proof.
  intros D PS l H; induction H as [|y x PS0 l0 Hyx HF IH]; intros Hi; constructor.
  - destruct y as [[p sh] P], x as [[a s] E]; simpl in Hyx. destruct Hyx as (-> & -> & HE & Ht).
    exists E. simpl. split; [apply Hi; left; reflexivity | auto].
  - apply IH. intros z Hz; apply Hi; right; auto.
Qed.

Lemma hrx5_B8I_I2_pool_entry: forall KA PS T, hrx5cr_pool KA PS T -> itable_wf T ->
  Forall (fun x => In (hs_addr (peer_addr4 x)) (saddrs (t_D T)) /\
                   e_peer (t_entry_d T (hs_addr (peer_addr4 x))) = peer_addr4 x) PS.
Proof.
  intros KA PS T (_ & Hp) (_ & _ & Hn & _).
  assert (HF: Forall (fun x => exists E, In (hs_addr (peer_addr4 x), Ews, E) (t_D T) /\ e_peer E = peer_addr4 x) PS).
  { eapply hrx5_B8I_I2_hs_in; [exact Hp|].
    intros y Hy. rewrite <- (firstn_skipn (length KA) (t_D T)). apply in_or_app; right; auto. }
  eapply Forall_impl; [|exact HF].
  intros x (E & HI & H1). split.
  - apply (in_map (fun '(x, _, _) => x) (t_D T) _) in HI; exact HI.
  - unfold t_entry_d, t_entry. rewrite (hrx5_B8I_I2_sfind_nodup _ _ _ _ Hn HI). exact H1.
Qed.

Lemma hrx5_B8I_I2_F2_sh {A: Type} (Rl: A -> val * share * entry -> Prop) (l1: list A) (l2: list (val * share * entry)) :
  (forall k x, Rl k x -> match x with (_, sh, _) => sh = Ews end) ->
  Forall2 Rl l1 l2 -> Forall (fun d => match d with (_, sh, _) => sh = Ews end) l2.
Proof.
  intros HR H; induction H as [|k x l1 l2 Hkx HF IH]; constructor; [exact (HR _ _ Hkx) | exact IH].
Qed.

Lemma hrx5_B8I_I2_pool_sh: forall KA PS T, hrx5cr_pool KA PS T ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T).
Proof.
  intros KA PS T (H1 & H2). rewrite <- (firstn_skipn (length KA) (t_D T)). apply Forall_app. split.
  - eapply hrx5_B8I_I2_F2_sh; [| exact H1]. intros k [[a sh] E] (_ & Hs & _). exact Hs.
  - eapply hrx5_B8I_I2_F2_sh; [| exact H2]. intros [[p s] P] [[a sh] E] (_ & Hs & _). exact Hs.
Qed.

Section Facts.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* everything the CHECK of I2 needs about the accepted peer, its node and its entry *)
Lemma hrx5_B8I_I2_facts R L NS PS KE T head nk M now a P t ck2 h2 :
  hrx5_inv x25519 R L NS PS KE T head nk -> itable_wf T ->
  hrx5ci_tgt x25519 aead_dec (hrx5_ID x25519 R) PS M now = Some (a, P, t, ck2, h2) ->
  exists N, In N (hnodes_snapped4 T NS PS) /\ hn_addr N = hrx5_nfind NS a /\
    hn_snap N = hsnap_val (hs_snap_cur T a P) /\
    sfind PS a = Some (Ews, P) /\ hs_ok (p_hs P) /\ hs_sid (p_hs P) = id_addr (l_wd L) /\
    In (hs_addr a) (saddrs (t_D T)) /\ Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) /\
    e_peer (t_entry_d T (hs_addr a)) = a.
Proof.
  intros Hinv Hwf Ht.
  destruct (hrx5_B8I_tgt_in x25519 aead_dec _ _ _ _ _ _ _ _ _ Ht) as [sh Hin].
  destruct Hinv as (Hpok & _ & Hnd & _ & Hpeers & _ & Hpool).
  pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hok.
  destruct Hok as (Hsh & _ & Hsid & Hhs & _). subst sh.
  destruct (hrx5_B8I_I2_split T PS NS a Ews P Hpeers Hnd Hin) as (NS1 & N & NS2 & E & Hfind & Hp).
  pose proof (proj1 (Forall_forall _ _) (hrx5_B8I_I2_pool_entry _ _ _ Hpool Hwf) _ Hin) as (HI & He).
  exists (hn_snapshot4 T N (a, Ews, P)).
  split; [rewrite E; apply in_or_app; right; left; reflexivity|].
  split; [cbn [hn_snapshot4 hn_addr]; auto|].
  split; [reflexivity|].
  split; [apply hrx5_B8I_I2_sfind; auto|].
  split; [exact Hhs|]. split; [exact Hsid|]. split; [exact HI|].
  split; [exact (hrx5_B8I_I2_pool_sh _ _ _ Hpool)|]. exact He.
Qed.

End Facts.
