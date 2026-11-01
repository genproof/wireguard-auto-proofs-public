(* law handshake_receive, phase B3: the pure lemmas of the invariant hrx5_inv
   used by the branches of B3 (statement hrx5_B3_lem_stmt, hrx5_B3_defs.v). *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Local Open Scope logic.

Local Open Scope Z_scope.

Section Lem.
Context {A: Type}.

Lemma hrx5_b3l_supd_forall (Q: val * share * A -> Prop) (l: list (val * share * A)) p sh v v' :
  Forall Q l -> sfind l p = Some (sh, v) -> Q (p, sh, v') -> Forall Q (supd l p v').
Proof.
  induction l as [|[[x shx] w] l IH]; simpl; intros HF Hf HQ; [discriminate|].
  inv HF. destruct (EqDec_val x p) as [->|Hne].
  - inv Hf. constructor; auto.
  - constructor; auto.
Qed.

Definition hrx5_b3l_as (y: val * share * A) : val * share := match y with (x, sh, _) => (x, sh) end.

Lemma hrx5_b3l_supd_as (l: list (val * share * A)) p v :
  map hrx5_b3l_as (supd l p v) = map hrx5_b3l_as l.
Proof.
  induction l as [|[[x shx] w] l IH]; simpl; [reflexivity|].
  destruct (EqDec_val x p); simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hrx5_b3l_sfind_in (l: list (val * share * A)) a :
  In a (map (fun y: val * share * A => match y with (x, _, _) => x end) l) ->
  exists sh v, sfind l a = Some (sh, v) /\ In (a, sh, v) l.
Proof.
  induction l as [|[[x shx] w] l IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a) as [->|Hne].
  - eauto.
  - destruct H as [H|H]; [congruence|]. destruct (IH H) as (sh & v & H1 & H2). eauto.
Qed.

End Lem.

Lemma hrx5_b3l_F2_proj {B C D: Type} (proj: C -> D) (R: B -> C -> Prop) :
  (forall a y1 y2, proj y1 = proj y2 -> R a y1 -> R a y2) ->
  forall A l1 l2, map proj l1 = map proj l2 -> Forall2 R A l1 -> Forall2 R A l2.
Proof.
  intros HR A l1 l2 Hm HF. revert l2 Hm. induction HF as [|a y A' l1' Hay HF IH]; intros l2 Hm.
  - destruct l2; [constructor | discriminate].
  - destruct l2 as [|y2 l2]; [discriminate|]. simpl in Hm. inv Hm. constructor; eauto.
Qed.

Lemma hrx5_b3l_F2_supd (PS: list (val * share * peer)) p v D :
  Forall2 hrx5cr_hs_ok PS D -> Forall2 hrx5cr_hs_ok (supd PS p v) D.
Proof.
  intros HF. revert p v. induction HF as [|x y PS' D' Hxy HF IH]; intros p v; simpl; [constructor|].
  destruct x as [[a sha] P]. destruct (EqDec_val a p); constructor; auto.
Qed.

Lemma hrx5_b3l_F2_in {B C: Type} (R: B -> C -> Prop) l1 l2 x :
  Forall2 R l1 l2 -> In x l1 -> exists y, In y l2 /\ R x y.
Proof.
  intros HF. induction HF as [|a b l1' l2' Hab HF IH]; simpl; intros H; [contradiction|].
  destruct H as [->|H]; [eauto|]. destruct (IH H) as (y & H1 & H2). eauto.
Qed.

Definition hrx5_b3l_ep (y: val * share * entry) : val * share * val * int :=
  match y with (x, sh, E) => (x, sh, e_peer E, e_type E) end.

Lemma hrx5_b3l_supd_ep (D: list (val * share * entry)) a sh E idx :
  sfind D a = Some (sh, E) ->
  map hrx5_b3l_ep (supd D a (mkEntry (e_peer E) (e_type E) idx)) = map hrx5_b3l_ep D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hf; [discriminate|].
  destruct (EqDec_val x a) as [->|Hne]; simpl.
  - inv Hf. reflexivity.
  - rewrite IH by auto. reflexivity.
Qed.

Lemma hrx5_b3l_pool_ins KA PS T a idx :
  hrx5cr_pool KA PS T -> hrx5cr_pool KA PS (t_insert T a idx).
Proof.
  unfold t_insert, t_set_index, t_entry, t_upd. cbn [t_D].
  destruct (sfind (t_D T) a) as [[sh E]|] eqn:Hf; [| intros H; exact H].
  cbn [t_D]. intros [H1 H2].
  pose proof (hrx5_b3l_supd_ep _ _ _ _ idx Hf) as Hm.
  assert (Hlen: length (supd (t_D T) a (mkEntry (e_peer E) (e_type E) idx)) = length (t_D T)).
  { rewrite <- (map_length hrx5_b3l_ep), Hm, map_length. reflexivity. }
  split.
  - eapply (hrx5_b3l_F2_proj hrx5_b3l_ep); [| | exact H1].
    + intros k [[x1 s1] E1] [[x2 s2] E2] He Hr. simpl in He. injection He as -> -> Hp Ht.
      simpl in *. rewrite <- Hp, <- Ht. exact Hr.
    + cbn [t_D]. rewrite <- !firstn_map, Hm. reflexivity.
  - eapply (hrx5_b3l_F2_proj hrx5_b3l_ep); [| | exact H2].
    + intros k [[x1 s1] E1] [[x2 s2] E2] He Hr. simpl in He. injection He as -> -> Hp Ht.
      destruct k as [[pk shk] Pk]. simpl in *. rewrite <- Hp, <- Ht. exact Hr.
    + cbn [t_D]. rewrite <- !skipn_map, Hm. reflexivity.
Qed.

Lemma hrx5_B3_lem x25519 : hrx5_B3_lem_stmt x25519.
Proof.
  unfold hrx5_B3_lem_stmt. split; [| split; [| split; [| split; [| split]]]].
  - intros R L NS PS KE T head nk p sh P P' (HF & Hwf & HND & Hch & Hnp & Hnk & Hpool) Hf Hok Hnx.
    pose proof (hrx5_b3l_supd_as PS p P') as Has.
    assert (Haddr: forall f: val * share -> val, map (fun y => f (hrx5_b3l_as y)) (supd PS p P') =
                                              map (fun y => f (hrx5_b3l_as y)) PS).
    { intros f. rewrite <- !(map_map hrx5_b3l_as f), Has. reflexivity. }
    assert (Hpa: map peer_addr4 (supd PS p P') = map peer_addr4 PS).
    { pose proof (Haddr fst) as X. etransitivity; [| etransitivity; [exact X|]];
        apply map_ext; intros [[? ?] ?]; reflexivity. }
    assert (Hca: map hrx5cr_paddr (supd PS p P') = map hrx5cr_paddr PS).
    { pose proof (Haddr fst) as X. etransitivity; [| etransitivity; [exact X|]];
        apply map_ext; intros [[? ?] ?]; reflexivity. }
    unfold hrx5_inv. split; [| split; [| split; [| split; [| split; [| split]]]]].
    + eapply hrx5_b3l_supd_forall; eauto.
    + unfold peers_wf in *. eapply hrx5_b3l_supd_forall; eauto.
      simpl. rewrite Forall_forall in Hwf. destruct (hrx5_b3l_sfind_in PS p) as (sh0 & v0 & H1 & H2).
      { clear - Hf. induction PS as [|[[x shx] w] PS IH]; simpl in *; [discriminate|].
        destruct (EqDec_val x p); [left; auto | right; auto]. }
      rewrite Hf in H1. inv H1. apply (Hwf _ H2).
    + rewrite Hpa. exact HND.
    + clear - Hch Hf Hnx. revert head Hch. induction PS as [|[[x shx] w] PS IH]; simpl in *; intros head Hch;
        [discriminate|].
      destruct (EqDec_val x p) as [->|Hne]; simpl.
      * inv Hf. rewrite Hnx. exact Hch.
      * destruct Hch as [Hh Hc]. split; [exact Hh|]. apply IH; auto.
    + unfold hnodes_peers4 in *. rewrite Hpa. exact Hnp.
    + exact Hnk.
    + destruct Hpool as [P1 P2]. split.
      * eapply Forall2_impl; [| exact P1]. intros k [[a sha] E] Hk. simpl in *. rewrite Hca. exact Hk.
      * apply hrx5_b3l_F2_supd. exact P2.
  - intros R L NS PS KE T head nk p sh P idx (HF & Hwf & HND & Hch & Hnp & Hnk & Hpool) Hf.
    unfold hrx5_inv. repeat (split; [assumption|]). apply hrx5_b3l_pool_ins. exact Hpool.
  - intros R L NS PS KE T head nk N (HF & Hwf & HND & Hch & Hnp & Hnk & [P1 P2]) HIn.
    assert (Hin: In (hn_p N) (map peer_addr4 PS)).
    { unfold hnodes_peers4 in Hnp. rewrite <- Hnp. apply in_map. exact HIn. }
    destruct (hrx5_b3l_sfind_in PS (hn_p N)) as (sh & P & H1 & H2).
    { exact Hin. }
    rewrite Forall_forall in HF. pose proof (HF _ H2) as Hok.
    assert (Hsh: sh = Ews) by (destruct Hok; auto). subst sh.
    exists P. split; [exact H1|]. split; [exact Hok|].
    destruct (hrx5_b3l_F2_in _ _ _ _ P2 H2) as ([[a sha] E] & Hy & Hr).
    simpl in Hr. destruct Hr as (-> & _).
    unfold saddrs. change (hs_addr (hn_p N)) with ((fun y: val * share * entry => match y with (x, _, _) => x end)
      (hs_addr (hn_p N), sha, E)).
    apply in_map. rewrite <- (firstn_skipn (length (map ke_addr KE)) (t_D T)). apply in_or_app. right. exact Hy.
  - intros R L NS PS KE T head nk (HF & Hwf & HND & Hch & Hnp & Hnk & Hpool) Hne.
    destruct Hnk as [Hn|Hn]; [contradiction|]. apply in_map_iff in Hn. destruct Hn as (N & H1 & H2). eauto.
  - intros R sec birth S idx H. exact H.
  - intros R sec birth S sec' ns H. exact H.
Qed.
