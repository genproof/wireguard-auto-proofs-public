(* law cookie_reply, phase P10, segment B (the ck_take loop): its pure list facts.
   CLs = the cnode list after the loop: every cnode (address, node address) with its peer's cookie; the k-th
   cnode's node is the k-th node from the end, whose peer is the k-th peer from the end. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
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
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.

Local Open Scope Z_scope.

(* the cnodes after the loop *)
Definition hcy5_p10_b_CLs (CL: list (val * val * option cookie)) (PS: list (val * share * peer))
  : list (val * val * option cookie) :=
  map (fun '(x, y) => (fst x, Some (p_cookie (snd y)))) (combine CL (rev PS)).

(* the k-th cnode (k from the head of CL): its node N (in the snapped node list, same addresses and peers),
   its peer (a, sh, P), its entry in CLs *)
Definition hcy5_p10_b_pick_stmt : Prop :=
  forall (T: tstate) (NS: list hnode4) (PS: list (val * share * peer)) (CL: list (val * val * option cookie))
    (k: nat) (c0 nd: val) (o: option cookie) (B: list (val * val * option cookie)),
  hnodes_peers4 NS PS -> hcy5_cl_nodes CL NS -> hcy5_cl_none CL ->
  skipn k CL = (c0, nd, o) :: B ->
  o = None /\ B = skipn (S k) CL /\
  exists N a sh P,
    In N (hnodes_snapped4 T NS PS) /\ hn_addr N = nd /\ hn_p N = a /\ In (a, sh, P) PS /\
    skipn k (hcy5_p10_b_CLs CL PS) = (c0, nd, Some (p_cookie P)) :: skipn (S k) (hcy5_p10_b_CLs CL PS).

(* after the loop *)
Definition hcy5_p10_b_end_stmt : Prop :=
  forall (NS: list hnode4) (PS: list (val * share * peer)) (CL: list (val * val * option cookie)),
  hnodes_peers4 NS PS -> hcy5_cl_nodes CL NS ->
  hcy5_cl_nodes (hcy5_p10_b_CLs CL PS) NS /\ hcy5_cl_snap (hcy5_p10_b_CLs CL PS) PS /\
  hcy5_chead (hcy5_p10_b_CLs CL PS) = hcy5_chead CL /\ length (hcy5_p10_b_CLs CL PS) = length CL.

Lemma hcy5_p10_b_pure_skipn_nth {A: Type} (l: list A) (k: nat) (x: A) (B: list A) :
  skipn k l = x :: B -> nth_error l k = Some x /\ skipn (S k) l = B.
Proof.
  revert k; induction l as [|y l IH]; intros k H.
  - destruct k; discriminate.
  - destruct k as [|k]; simpl in *.
    + inversion H; subst; auto.
    + apply IH; exact H.
Qed.

Lemma hcy5_p10_b_pure_nth_skipn {A: Type} (l: list A) (k: nat) (x: A) :
  nth_error l k = Some x -> skipn k l = x :: skipn (S k) l.
Proof.
  revert k; induction l as [|y l IH]; intros k H.
  - destruct k; discriminate.
  - destruct k as [|k]; simpl in *.
    + inversion H; subst; auto.
    + apply IH; exact H.
Qed.

Lemma hcy5_p10_b_pure_skipn_map {A B: Type} (f: A -> B) (l: list A) (k: nat) :
  skipn k (map f l) = map f (skipn k l).
Proof.
  revert k; induction l as [|y l IH]; intros k; destruct k; simpl; auto.
Qed.

Lemma hcy5_p10_b_pure_skipn_combine {A B: Type} (l1: list A) (l2: list B) (k: nat) :
  skipn k (combine l1 l2) = combine (skipn k l1) (skipn k l2).
Proof.
  revert k l2; induction l1 as [|y l1 IH]; intros k l2.
  - destruct k; reflexivity.
  - destruct k as [|k]; destruct l2 as [|z l2]; simpl; auto.
    symmetry; apply combine_nil.
Qed.

Lemma hcy5_p10_b_pure_nth_combine {A B: Type} (l1: list A) (l2: list B) (k: nat) (x: A) (y: B) :
  nth_error l1 k = Some x -> nth_error l2 k = Some y -> nth_error (combine l1 l2) k = Some (x, y).
Proof.
  revert k l2; induction l1 as [|a l1 IH]; intros k l2 H1 H2.
  - destruct k; discriminate.
  - destruct l2 as [|b l2]; [destruct k; discriminate|].
    destruct k as [|k]; simpl in *.
    + inversion H1; inversion H2; subst; auto.
    + apply IH; auto.
Qed.

Lemma hcy5_p10_b_pure_combine_app {A B: Type} (l1 l1': list A) (l2 l2': list B) :
  length l1 = length l2 -> combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
Proof.
  revert l2; induction l1 as [|a l1 IH]; intros l2 H.
  - destruct l2; [reflexivity|discriminate].
  - destruct l2 as [|b l2]; [discriminate|].
    simpl in *. rewrite IH; auto.
Qed.

Lemma hcy5_p10_b_pure_combine_rev {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 -> combine (rev l1) (rev l2) = rev (combine l1 l2).
Proof.
  revert l2; induction l1 as [|a l1 IH]; intros l2 H.
  - destruct l2; [reflexivity|discriminate].
  - destruct l2 as [|b l2]; [discriminate|].
    simpl in *. rewrite hcy5_p10_b_pure_combine_app.
    + rewrite IH; auto.
    + rewrite !rev_length; auto.
Qed.

Lemma hcy5_p10_b_pure_map_fst_combine {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 -> map fst (combine l1 l2) = l1.
Proof.
  revert l2; induction l1 as [|a l1 IH]; intros l2 H.
  - reflexivity.
  - destruct l2 as [|b l2]; [discriminate|].
    simpl in *. rewrite IH; auto.
Qed.

Lemma hcy5_p10_b_pure_map_snd_combine {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 -> map snd (combine l1 l2) = l2.
Proof.
  revert l2; induction l1 as [|a l1 IH]; intros l2 H.
  - destruct l2; [reflexivity|discriminate].
  - destruct l2 as [|b l2]; [discriminate|].
    simpl in *. rewrite IH; auto.
Qed.

Lemma hcy5_p10_b_pure_len (NS: list hnode4) (PS: list (val * share * peer))
    (CL: list (val * val * option cookie)) :
  hnodes_peers4 NS PS -> hcy5_cl_nodes CL NS -> length CL = length (rev PS).
Proof.
  intros HP [HN _].
  apply (f_equal (@length _)) in HP. apply (f_equal (@length _)) in HN.
  rewrite !map_length in HP. rewrite map_length, rev_length, map_length in HN.
  rewrite rev_length. congruence.
Qed.

Lemma hcy5_p10_b_pure_fst (CL: list (val * val * option cookie)) (PS: list (val * share * peer)) :
  length CL = length (rev PS) -> map fst (hcy5_p10_b_CLs CL PS) = map fst CL.
Proof.
  intros H. unfold hcy5_p10_b_CLs. rewrite map_map.
  rewrite <- (hcy5_p10_b_pure_map_fst_combine CL (rev PS)) at 2 by exact H.
  rewrite map_map. apply map_ext. intros [x y]; reflexivity.
Qed.

Lemma hcy5_p10_b_pure_all : hcy5_p10_b_pick_stmt /\ hcy5_p10_b_end_stmt.
Proof.
  split.
  - intros T NS PS CL k c0 nd o B HP HN H0 HS.
    pose proof (hcy5_p10_b_pure_len NS PS CL HP HN) as HL.
    destruct (hcy5_p10_b_pure_skipn_nth CL k _ B HS) as [Hk HB].
    assert (Hlt: (k < length CL)%nat) by (apply nth_error_Some; congruence).
    split.
    { unfold hcy5_cl_none in H0; rewrite Forall_forall in H0. apply (H0 (c0, nd, o)). eapply nth_error_In; eauto. }
    split; [symmetry; exact HB|].
    destruct (nth_error (rev PS) k) as [[[a sh] P]|] eqn:EP;
      [|apply nth_error_None in EP; lia].
    destruct (nth_error (rev NS) k) as [N0|] eqn:EN;
      [|apply nth_error_None in EN;
        destruct HN as [HN _]; apply (f_equal (@length _)) in HN;
        rewrite map_length, rev_length, map_length in HN; rewrite rev_length in EN; lia].
    destruct HN as [HN _].
    assert (Haddr: hn_addr N0 = nd).
    { assert (E1: nth_error (map (fun x => snd (fst x)) CL) k = Some nd)
        by (rewrite nth_error_map, Hk; reflexivity).
      rewrite HN, <- map_rev, nth_error_map, EN in E1. simpl in E1. congruence. }
    assert (Hp: hn_p N0 = a).
    { unfold hnodes_peers4 in HP. apply (f_equal (@rev _)) in HP. rewrite <- !map_rev in HP.
      assert (E1: nth_error (map hn_p (rev NS)) k = Some (hn_p N0))
        by (rewrite nth_error_map, EN; reflexivity).
      rewrite HP, nth_error_map, EP in E1. simpl in E1. congruence. }
    assert (HLNS: length NS = length PS).
    { unfold hnodes_peers4 in HP. apply (f_equal (@length _)) in HP. rewrite !map_length in HP. exact HP. }
    exists (hn_snapshot4 T N0 (a, sh, P)), a, sh, P.
    split.
    { unfold hnodes_snapped4.
      apply (in_map (fun '(N, x) => hn_snapshot4 T N x) (combine NS PS) (N0, (a, sh, P))).
      apply in_rev. rewrite <- hcy5_p10_b_pure_combine_rev by exact HLNS.
      eapply nth_error_In. apply hcy5_p10_b_pure_nth_combine; eauto. }
    split; [simpl; auto|].
    split; [simpl; auto|].
    split.
    { apply in_rev. eapply nth_error_In; eauto. }
    unfold hcy5_p10_b_CLs.
    rewrite !hcy5_p10_b_pure_skipn_map, !hcy5_p10_b_pure_skipn_combine.
    rewrite HS, HB, (hcy5_p10_b_pure_nth_skipn _ _ _ EP). reflexivity.
  - intros NS PS CL HP HN.
    pose proof (hcy5_p10_b_pure_len NS PS CL HP HN) as HL.
    pose proof (hcy5_p10_b_pure_fst CL PS HL) as HF.
    split; [|split; [|split]].
    + destruct HN as [HN HD]. split.
      * rewrite <- HN.
        transitivity (map snd (map fst (hcy5_p10_b_CLs CL PS))); [rewrite map_map; reflexivity|].
        rewrite HF, map_map. reflexivity.
      * replace (map (fun x => fst (fst x)) (hcy5_p10_b_CLs CL PS))
          with (map fst (map fst (hcy5_p10_b_CLs CL PS))) by (rewrite map_map; reflexivity).
        rewrite HF, map_map. exact HD.
    + unfold hcy5_cl_snap, hcy5_p10_b_CLs. rewrite map_map, <- map_rev.
      rewrite <- (hcy5_p10_b_pure_map_snd_combine CL (rev PS)) at 2 by exact HL.
      rewrite map_map. apply map_ext. intros [x y]; reflexivity.
    + unfold hcy5_p10_b_CLs. destruct CL as [|[[c nd] o] CL']; [reflexivity|].
      destruct (rev PS) as [|y RPS]; [discriminate|]. reflexivity.
    + unfold hcy5_p10_b_CLs. rewrite map_length, combine_length. lia.
Qed.

Lemma hcy5_p10_b_pick : hcy5_p10_b_pick_stmt.
Proof. exact (proj1 hcy5_p10_b_pure_all). Qed.

Lemma hcy5_p10_b_end : hcy5_p10_b_end_stmt.
Proof. exact (proj2 hcy5_p10_b_pure_all). Qed.
