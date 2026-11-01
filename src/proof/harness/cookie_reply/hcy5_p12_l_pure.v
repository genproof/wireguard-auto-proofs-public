(* law cookie_reply, phase P12, segment L:
   the pure fact behind the ck_same loop (statement 70): the k-th cnode's node, its peer, and that peer is
   unchanged by the consumption unless the cnode is the target.  Port of v1's hcy4_p12_l_pure.v. *)
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
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.

Local Open Scope Z_scope.

(* helpers *)
Lemma hcy5_p12_l_pure_skipn_nth {A: Type} (l: list A) (k: nat) (x: A) (B: list A) :
  skipn k l = x :: B -> nth_error l k = Some x.
Proof.
  revert l; induction k as [|k IH]; intros [|y l] H; simpl in *; try discriminate; auto; congruence.
Qed.

Lemma hcy5_p12_l_pure_combine {A B: Type} (l1: list A) (l2: list B) (n: nat) (a: A) (b: B) :
  nth_error l1 n = Some a -> nth_error l2 n = Some b -> nth_error (combine l1 l2) n = Some (a, b).
Proof.
  revert l1 l2; induction n as [|n IH]; intros [|x l1] [|y l2]; simpl; intros H1 H2;
    try discriminate; auto; congruence.
Qed.

Lemma hcy5_p12_l_pure_inj {A B: Type} (f: A -> B) (l: list A) (x y: A) :
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; simpl; intros Hnd Hx Hy Hf; [contradiction|].
  inversion Hnd as [|? ? Hnin Hnd']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
  - exfalso; apply Hnin; rewrite Hf; apply in_map; auto.
  - exfalso; apply Hnin; rewrite <- Hf; apply in_map; auto.
Qed.

Lemma hcy5_p12_l_pure_nodepeer (NS: list hnode4) (N: hnode4) :
  NoDup (map hn_addr NS) -> In N NS -> hcy5_nodepeer NS (hn_addr N) = hn_p N.
Proof.
  intros Hnd Hin. unfold hcy5_nodepeer.
  destruct (find (fun N' => if eq_dec (hn_addr N') (hn_addr N) then true else false) NS) as [N'|] eqn:E.
  - apply find_some in E as [Hin' He].
    destruct (eq_dec (hn_addr N') (hn_addr N)) as [e|]; [|discriminate].
    rewrite (hcy5_p12_l_pure_inj hn_addr NS N' N Hnd Hin' Hin e). reflexivity.
  - exfalso. pose proof (find_none _ _ E N Hin) as H. cbv beta in H.
    destruct (eq_dec (hn_addr N) (hn_addr N)); [discriminate|contradiction].
Qed.

Lemma hcy5_p12_l_pure_cpeers (NS: list hnode4) (CL: list (val * val * option cookie)) :
  NoDup (map hn_addr NS) -> map (fun x => snd (fst x)) CL = rev (map hn_addr NS) ->
  map (fun x => hcy5_nodepeer NS (snd (fst x))) CL = rev (map hn_p NS).
Proof.
  intros Hnd H.
  transitivity (map (hcy5_nodepeer NS) (map (fun x : val * val * option cookie => snd (fst x)) CL)).
  { rewrite map_map. reflexivity. }
  rewrite H, map_rev, map_map. f_equal.
  apply map_ext_in. intros N Hin. apply hcy5_p12_l_pure_nodepeer; auto.
Qed.

Lemma hcy5_p12_l_pure_cfind (NS: list hnode4) (CL: list (val * val * option cookie)) (k: nat)
  c0 nd o B :
  NoDup (map (fun x => hcy5_nodepeer NS (snd (fst x))) CL) ->
  skipn k CL = (c0, nd, o) :: B ->
  hcy5_cfind NS CL (hcy5_nodepeer NS nd) = c0.
Proof.
  revert CL; induction k as [|k IH]; intros CL Hnd Hs.
  - simpl in Hs; subst CL. simpl. destruct (EqDec_val (hcy5_nodepeer NS nd) (hcy5_nodepeer NS nd)); [reflexivity|contradiction].
  - destruct CL as [|[[c1 nd1] o1] CL]; simpl in Hs; [discriminate|].
    simpl in Hnd. inversion Hnd as [|? ? Hnin Hnd']; subst.
    simpl. destruct (EqDec_val (hcy5_nodepeer NS nd1) (hcy5_nodepeer NS nd)) as [e|ne].
    + exfalso. apply Hnin. rewrite e.
      assert (Hi: In (c0, nd, o) CL).
      { rewrite <- (firstn_skipn k CL), Hs. apply in_or_app; right; left; auto. }
      apply (in_map (fun x : val * val * option cookie => hcy5_nodepeer NS (snd (fst x))) _ _ Hi).
    + apply IH; auto.
Qed.

Lemma hcy5_p12_l_pure_supd {A: Type} (l: list (val * share * A)) (a: val) (v: A) x sh w :
  In (x, sh, w) l -> x <> a -> In (x, sh, w) (supd l a v).
Proof.
  induction l as [|[[y sh'] w'] l IH]; simpl; intros Hin Hne; auto.
  destruct (EqDec_val y a) as [e|ne].
  - subst y. destruct Hin as [Heq|Hin]; [inversion Heq; congruence|]. right; auto.
  - destruct Hin as [Heq|Hin]; [left; auto|right; auto].
Qed.

(* The k-th cnode (c0, nd, o) of CL: its node N (in the snapped node list, the one the SEP holds) at nd,
   N's peer a, the peer (a, Ews, P) of PS, the snapshot o = P's cookie; and unless c0 is the target of the
   consumption result res, the peer is unchanged in peers_after PS res.
   Why: hcy5_cl_nodes / hcy5_cl_snap say the cnodes are the nodes / peers' cookies in reverse order;
   hcy5_lists_ok gives hnodes_peers4 NS PS (map hn_p NS = map peer_addr4 PS), NoDup peer addresses and
   NoDup node addresses, every share Ews.  hn_snapshot4 keeps hn_addr and hn_p.  If res = Some (a', _)
   with a' = a, hcy5_cfind NS CL a = c0 (the cnodes' node peers hcy5_nodepeer NS nd are pairwise
   distinct), so c0 = target; if a' <> a, supd PS a' _ keeps (a, Ews, P); if res = None, nothing changed. *)
Lemma hcy5_p12_l_pick (L: hcy5_loc) (KS: list val) (T: tstate) (NS: list hnode4) (PS: list (val * share * peer))
  (CL: list (val * val * option cookie)) (res: option (val * peer)) (k: nat) c0 nd o B :
  hcy5_lists_ok L KS NS PS -> hcy5_cl_nodes CL NS -> hcy5_cl_snap CL PS ->
  skipn k CL = (c0, nd, o) :: B ->
  exists N a P,
    In N (hnodes_snapped4 T NS PS) /\ hn_addr N = nd /\ hn_p N = a /\ In (a, Ews, P) PS /\
    o = Some (p_cookie P) /\
    (c0 <> hcy5_tgt NS CL res -> In (a, Ews, P) (peers_after PS res)).
Proof.
  intros [Hok [Hpe [HndP [HndN _]]]] [Hcn HndC] Hcs Hsk.
  pose proof (hcy5_p12_l_pure_skipn_nth _ _ _ _ Hsk) as Hk.
  assert (HlC: length CL = length NS).
  { apply (f_equal (@length _)) in Hcn. rewrite map_length, rev_length, map_length in Hcn. exact Hcn. }
  assert (HlP: length PS = length NS).
  { unfold hnodes_peers4 in Hpe. apply (f_equal (@length _)) in Hpe. rewrite !map_length in Hpe. lia. }
  assert (Hklt: (k < length NS)%nat).
  { rewrite <- HlC. apply nth_error_Some. congruence. }
  assert (Hnd: nth_error (map hn_addr NS) (length NS - S k) = Some nd).
  { assert (E := f_equal (fun l => nth_error l k) Hcn). cbv beta in E.
    rewrite nth_error_map, Hk, nth_error_rev, map_length in E.
    destruct (Nat.ltb_spec k (length NS)); [|lia]. simpl in E. rewrite <- E. reflexivity. }
  assert (Ho: nth_error (map (fun x => Some (p_cookie (snd x))) PS) (length NS - S k) = Some o).
  { assert (E := f_equal (fun l => nth_error l k) Hcs). cbv beta in E.
    rewrite nth_error_map, Hk, nth_error_rev, map_length, HlP in E.
    destruct (Nat.ltb_spec k (length NS)); [|lia]. simpl in E. rewrite <- E. reflexivity. }
  set (j := (length NS - S k)%nat) in *.
  rewrite nth_error_map in Hnd, Ho.
  destruct (nth_error NS j) as [N0|] eqn:EN; [|discriminate].
  destruct (nth_error PS j) as [[[a sh] P]|] eqn:EP; [|discriminate].
  simpl in Hnd, Ho. injection Hnd as Hnd. injection Ho as Ho.
  assert (Ha: hn_p N0 = a).
  { assert (E := f_equal (fun l => nth_error l j) Hpe). cbv beta in E.
    rewrite !nth_error_map, EN, EP in E. simpl in E. injection E as E. exact E. }
  assert (HinP: In (a, sh, P) PS) by (eapply nth_error_In; eauto).
  assert (Hsh: sh = Ews).
  { rewrite Forall_forall in Hok. apply Hok in HinP. simpl in HinP. tauto. }
  subst sh.
  assert (HinN: In N0 NS) by (eapply nth_error_In; eauto).
  exists (hn_snapshot4 T N0 (a, Ews, P)), a, P.
  assert (Hsa: hn_addr (hn_snapshot4 T N0 (a, Ews, P)) = hn_addr N0 /\
               hn_p (hn_snapshot4 T N0 (a, Ews, P)) = hn_p N0).
  { unfold hn_snapshot4. simpl; auto. }
  destruct Hsa as [Hsa1 Hsa2].
  split; [|split; [|split; [|split; [|split]]]].
  - unfold hnodes_snapped4. apply in_map_iff. exists (N0, (a, Ews, P)). split; [reflexivity|].
    eapply nth_error_In. apply hcy5_p12_l_pure_combine; eauto.
  - rewrite Hsa1; auto.
  - rewrite Hsa2; auto.
  - exact HinP.
  - simpl in Ho. symmetry; exact Ho.
  - intros Hne. destruct res as [[a' P'']|]; simpl; [|exact HinP].
    destruct (eq_dec a a') as [e|ne].
    + subst a'. exfalso. apply Hne. unfold hcy5_tgt.
      assert (Hnp: hcy5_nodepeer NS nd = a).
      { rewrite <- Hnd, <- Ha. apply hcy5_p12_l_pure_nodepeer; auto. }
      rewrite <- Hnp. symmetry. eapply hcy5_p12_l_pure_cfind; [|exact Hsk].
      rewrite (hcy5_p12_l_pure_cpeers NS CL HndN Hcn). apply NoDup_rev.
      unfold hnodes_peers4 in Hpe. rewrite Hpe. exact HndP.
    + apply hcy5_p12_l_pure_supd; auto.
Qed.
