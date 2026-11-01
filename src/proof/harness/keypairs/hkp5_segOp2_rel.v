(* law keypairs: the harness's model after op 2 (expire)
   against the kernel's.  The kernel: expire_model (prot_model3.v): the handshake zeroed and its entry unhashed
   (t_remove), the sending keys of next and current invalidated (in that order).  The harness:
   `if (s_next) s_next->send_valid = false; if (s_cur) s_cur->send_valid = false;` = hk5o2_inv1 on s_next, then
   on s_cur.  Pure Coq.  Adapted from v1's hkp4_segOp2_rel. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.keypairs.hkp5_model.

(* the harness's `m->send_valid = false` on the live node m (NULL: nothing) *)
Definition hk5o2_inv1 (ML: list (val * hk5_mk)) (m: val) : list (val * hk5_mk) :=
  if eq_dec m nullval then ML else
  match afind ML m with Some M => aupd ML m (m5_invalidate_send M) | None => ML end.

(* the kernel's `inv` of expire_model *)
Definition hk5o2_invK (KS: list (val * keypair)) (k: val) : list (val * keypair) :=
  if eq_dec k nullval then KS else
  match afind KS k with Some K => aupd KS k (kp_invalidate_send K) | None => KS end.

Lemma hk5o2_map_fst_aupd {A: Type} (l: list (val * A)) a v : map fst (aupd l a v) = map fst l.
Proof.
  induction l as [|[x w] l IH]; simpl; auto.
  if_tac; simpl; f_equal; auto.
Qed.

Lemma hk5o2_afind_in {A: Type} (l: list (val * A)) a v : afind l a = Some v -> In a (map fst l).
Proof.
  induction l as [|[x w] l IH]; simpl; [discriminate|].
  if_tac; intros E; [left; auto | right; auto].
Qed.

Lemma hk5o2_afind_aupd {A: Type} (l: list (val * A)) a b v :
  afind (aupd l a v) b =
  if eq_dec a b then match afind l a with Some _ => Some v | None => None end else afind l b.
Proof.
  induction l as [|[x w] l IH]; simpl.
  - if_tac; auto.
  - repeat match goal with |- context [if ?c then _ else _] => destruct c; try subst end; simpl; try congruence; auto;
    repeat match goal with |- context [if ?c then _ else _] => destruct c; try subst end; try congruence; auto;
    rewrite IH; repeat match goal with |- context [if ?c then _ else _] => destruct c end; congruence.
Qed.

Lemma hk5o2_map_fst_inv1 ML m : map fst (hk5o2_inv1 ML m) = map fst ML.
Proof.
  unfold hk5o2_inv1. destruct (eq_dec m nullval); auto.
  destruct (afind ML m); auto. apply hk5o2_map_fst_aupd.
Qed.

Lemma hk5o2_map_fst_invK KS k : map fst (hk5o2_invK KS k) = map fst KS.
Proof.
  unfold hk5o2_invK. destruct (eq_dec k nullval); auto.
  destruct (afind KS k); auto. apply hk5o2_map_fst_aupd.
Qed.

Lemma hk5o2_slot_kp_inv1 ML m x : hk5_slot_kp (hk5o2_inv1 ML m) x = hk5_slot_kp ML x.
Proof.
  unfold hk5o2_inv1. destruct (eq_dec m nullval); auto.
  destruct (afind ML m) as [M|] eqn:E; auto.
  unfold hk5_slot_kp. destruct (eq_dec x nullval); auto.
  rewrite hk5o2_afind_aupd. destruct (eq_dec m x); auto.
  subst x. rewrite E. reflexivity.
Qed.

Lemma hk5o2_Forall_aupd {A: Type} (Q: val * A -> Prop) (g: A -> A) l a M :
  Forall Q l -> afind l a = Some M -> (forall x w, Q (x, w) -> Q (x, g w)) -> Forall Q (aupd l a (g M)).
Proof.
  intros HF. induction HF as [|[x w] l Hx HF IH]; simpl; [discriminate|].
  intros E Hg. destruct (EqDec_val x a).
  - inversion E; subst. constructor; auto.
  - constructor; auto.
Qed.

Lemma hk5o2_Forall_inv1 (Q: val * hk5_mk -> Prop) ML m :
  Forall Q ML -> (forall x w, Q (x, w) -> Q (x, m5_invalidate_send w)) -> Forall Q (hk5o2_inv1 ML m).
Proof.
  intros HF Hg. unfold hk5o2_inv1. destruct (eq_dec m nullval); auto.
  destruct (afind ML m) as [M|] eqn:E; auto.
  apply (hk5o2_Forall_aupd Q m5_invalidate_send); auto.
Qed.

Lemma hk5o2_match_inv p T M K :
  hk5_match p T M K -> hk5_match p T (m5_invalidate_send M) (kp_invalidate_send K).
Proof.
  unfold hk5_match. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  destruct K as [ks ksc kr krc kbt kri ki krf kid]; cbn in *.
  rewrite H4. cbn. repeat split; auto.
Qed.

Lemma hk5o2_f2_upd p T : forall ML KS m M,
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  NoDup (map fst KS) -> afind ML m = Some M ->
  exists K, afind KS (m5_kp M) = Some K /\
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y))
    (aupd ML m (m5_invalidate_send M)) (aupd KS (m5_kp M) (kp_invalidate_send K)).
Proof.
  intros ML KS m M HF. induction HF as [|[x w] [k K0] ML KS Hxy HF IH]; simpl; [discriminate|].
  intros ND E. destruct Hxy as [Hk Hm]; cbn in Hk, Hm. subst k.
  destruct (EqDec_val x m) as [Hxm|Hxm].
  - inversion E; subst M. exists K0.
    destruct (EqDec_val (m5_kp w) (m5_kp w)); [|congruence].
    split; auto. constructor; auto. cbn. split; auto. apply hk5o2_match_inv; auto.
  - inversion ND as [|? ? Hnin ND']; subst.
    destruct (IH ND' E) as [K [EK F]]. exists K.
    pose proof (hk5o2_afind_in _ _ _ EK) as Hin.
    destruct (EqDec_val (m5_kp w) (m5_kp M)) as [Heq|Heq].
    + exfalso. apply Hnin. rewrite Heq. exact Hin.
    + split; [exact EK|]. constructor; [split; auto|exact F].
Qed.

Lemma hk5o2_step p T ML KS m :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  NoDup (map fst KS) -> ~ In nullval (map fst KS) ->
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y))
    (hk5o2_inv1 ML m) (hk5o2_invK KS (hk5_slot_kp ML m)).
Proof.
  intros HF ND NN. unfold hk5o2_inv1, hk5_slot_kp, hk5o2_invK.
  destruct (eq_dec m nullval).
  - destruct (eq_dec nullval nullval); [auto|congruence].
  - destruct (afind ML m) as [M|] eqn:E.
    + destruct (hk5o2_f2_upd p T ML KS m M HF ND E) as [K [EK F]].
      destruct (eq_dec (m5_kp M) nullval) as [Hn|Hn].
      * exfalso. apply NN. rewrite <- Hn. eapply hk5o2_afind_in; eauto.
      * rewrite EK. exact F.
    + destruct (eq_dec nullval nullval); [auto|congruence].
Qed.

Lemma hk5o2_in_vremove x a l : In x (vremove a l) <-> In x l /\ x <> a.
Proof.
  induction l as [|y l IH]; simpl; [tauto|].
  destruct (EqDec_val y a); simpl; rewrite IH; split; intros Hx.
  - tauto.
  - destruct Hx as [[Hx|Hx] Hn]; [congruence|tauto].
  - destruct Hx as [Hx|Hx]; [subst; tauto|tauto].
  - tauto.
Qed.

Lemma hk5o2_nodup_vremove {B: Type} (f: val -> B) a l : NoDup (map f l) -> NoDup (map f (vremove a l)).
Proof.
  induction l as [|y l IH]; simpl; auto.
  intros ND. inversion ND as [|? ? Hnin ND']; subst.
  destruct (EqDec_val y a); simpl; auto.
  constructor; auto. intro Hin. apply Hnin.
  apply in_map_iff in Hin. destruct Hin as [z [Hz Hin]].
  apply hk5o2_in_vremove in Hin. apply in_map_iff. exists z; tauto.
Qed.

Lemma hk5o2_vin_remove a hs l : a <> hs -> vin a (vremove hs l) = vin a l.
Proof.
  intros Hne. unfold vin.
  destruct (in_dec eq_dec a (vremove hs l)) as [Hi|Hi];
  destruct (in_dec eq_dec a l) as [Hj|Hj]; auto;
  rewrite hk5o2_in_vremove in Hi; tauto.
Qed.

Lemma hk5o2_f2_remove p T hs (ML: list (val * hk5_mk)) (KS: list (val * keypair)) :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  ~ In hs (map fst KS) ->
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p (t_remove T hs) (snd x) (snd y)) ML KS.
Proof.
  intros HF. induction HF as [|x y ML KS Hxy HF IH]; simpl; intros Hnin; constructor; auto.
  destruct Hxy as [Hk Hm]. split; auto.
  unfold hk5_match in *. unfold t_remove; cbn [t_D t_L].
  destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  refine (conj H1 (conj H2 (conj _ (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 H10))))))))).
  rewrite <- H3. apply hk5o2_vin_remove.
  rewrite <- Hk; intro E; apply Hnin; rewrite <- E; left; auto.
Qed.

Lemma hk5o2_pool_remove p OD OH KS KS' T :
  map fst KS' = map fst KS -> itable_wf (t_remove T (hs_addr p)) ->
  hk5_pool p OD OH KS T -> hk5_pool p OD OH KS' (t_remove T (hs_addr p)).
Proof.
  intros MK Hwf (Hadr & Hn1 & Hn2 & Hdis & Hhs & HOD & HND & _).
  unfold hk5_pool, t_remove in *; cbn [t_D t_L] in *. rewrite MK.
  refine (conj Hadr (conj Hn1 (conj Hn2 (conj Hdis (conj Hhs (conj _ (conj _ Hwf))))))).
  - rewrite Forall_forall in HOD |- *. intros [[a sh] E] Hx. destruct (HOD _ Hx) as [Hf Hv].
    split; [exact Hf|]. rewrite hk5o2_vin_remove; [exact Hv|].
    intros ->. apply Hn2. unfold saddrs.
    exact (in_map (fun '(x, _, _) => x) OD (hs_addr p, sh, E) Hx).
  - unfold t_indices in *. cbn [t_D t_L] in *.
    apply (hk5o2_nodup_vremove (fun a => match t_entry T a with Some E => e_index E | None => Int.zero end)).
    exact HND.
Qed.

(* the relation survives op 2 *)
Lemma hk5o2_rel p OD OH H P KS T now :
  itable_wf (t_remove T (hs_addr p)) ->
  hk5_rel p OD OH H P KS T ->
  hk5_rel p OD OH (h5_set_ML H (hk5o2_inv1 (hk5o2_inv1 (h5_ML H) (h5_sn H)) (h5_sc H)))
    (fst (fst (expire_model P (hs_addr p) KS T now)))
    (snd (fst (expire_model P (hs_addr p) KS T now)))
    (snd (expire_model P (hs_addr p) KS T now)).
Proof.
  intros Hwf1 Hrel.
  destruct Hrel as ((F2 & ND1 & NN1 & ND2 & NN2 & FR & Fcnt & Fhash & Hpool) & NDsl & Hp & Hc & Hn).
  assert (E: expire_model P (hs_addr p) KS T now =
    (p_set_lsh (p_set_hs P (hs_zero (p_hs P))) (reset_lsh now),
     hk5o2_invK (hk5o2_invK KS (p_next P)) (p_cur P), t_remove T (hs_addr p))) by reflexivity.
  rewrite E; cbn [fst snd]; clear E.
  pose proof Hpool as (_ & HnKS & _).
  assert (F2T: Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p (t_remove T (hs_addr p)) (snd x) (snd y))
                 (h5_ML H) KS) by (apply hk5o2_f2_remove; auto).
  assert (F2a := hk5o2_step _ _ _ _ (h5_sn H) F2T ND2 NN2).
  rewrite <- Hn in F2a.
  assert (MK1: map fst (hk5o2_invK KS (p_next P)) = map fst KS) by apply hk5o2_map_fst_invK.
  assert (F2b := hk5o2_step _ _ _ _ (h5_sc H) F2a ltac:(rewrite MK1; auto) ltac:(rewrite MK1; auto)).
  rewrite hk5o2_slot_kp_inv1, <- Hc in F2b.
  assert (MK2: map fst (hk5o2_invK (hk5o2_invK KS (p_next P)) (p_cur P)) = map fst KS)
    by (rewrite !hk5o2_map_fst_invK; auto).
  assert (MM: map fst (hk5o2_inv1 (hk5o2_inv1 (h5_ML H) (h5_sn H)) (h5_sc H)) = map fst (h5_ML H))
    by (rewrite !hk5o2_map_fst_inv1; auto).
  unfold hk5_rel, hk5_core, hk5_slots, h5_set_ML in *; cbn [h5_ML h5_sp h5_sc h5_sn] in *.
  rewrite MM, MK2, !hk5o2_slot_kp_inv1.
  split; [|split; [exact NDsl | split; [exact Hp | split; [exact Hc | exact Hn]]]].
  split; [exact F2b|]. split; [exact ND1|]. split; [exact NN1|]. split; [exact ND2|]. split; [exact NN2|].
  split; [exact FR|].
  split.
  { apply hk5o2_Forall_inv1; [apply hk5o2_Forall_inv1; [exact Fcnt|]|]; intros x w HQ; exact HQ. }
  split.
  { apply hk5o2_Forall_inv1; [apply hk5o2_Forall_inv1; [exact Fhash|]|]; intros x w HQ; exact HQ. }
  apply hk5o2_pool_remove with (KS := KS); auto.
Qed.
