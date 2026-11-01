(* v2, law handshake_receive, B8 R B part L: helpers for CLR. The access lemmas are copies of
   hrx5_B8_R_B_K_sep.v renamed hrx5_B8RBK_ -> hrx5_B8RBL_. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Local Open Scope logic.
Local Open Scope logic.

Notation W := W_handshake_receive.
#[export] Instance hrx5_B8RBL_cceKW : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

(* ---- generic ---- *)
Definition hrx5_B8RBL_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B8RBL_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hrx5_B8RBL_acc_refl Q : hrx5_B8RBL_acc Q Q.
Proof.
  unfold hrx5_B8RBL_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B8RBL_acc_eq Q A : Q = A -> hrx5_B8RBL_acc Q A.
Proof. intros ->. apply hrx5_B8RBL_acc_refl. Qed.

Lemma hrx5_B8RBL_acc_l Q A F : hrx5_B8RBL_acc Q A -> hrx5_B8RBL_acc Q (A * F).
Proof.
  unfold hrx5_B8RBL_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B8RBL_acc_r Q A F : hrx5_B8RBL_acc Q A -> hrx5_B8RBL_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B8RBL_acc_l, H. Qed.

Lemma hrx5_B8RBL_acc_prop Q (c: Prop) A : (c -> hrx5_B8RBL_acc Q A) -> hrx5_B8RBL_acc Q (!! c && A).
Proof.
  unfold hrx5_B8RBL_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8RBL_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_B8RBL_acc Q (A x)) -> hrx5_B8RBL_acc Q (EX x, A x).
Proof.
  unfold hrx5_B8RBL_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply (exp_right x), derives_refl.
Qed.

Lemma hrx5_B8RBL_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hrx5_B8RBL_acc Q A) -> hrx5_B8RBL_acc Q A.
Proof.
  unfold hrx5_B8RBL_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hrx5_B8RBL_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hrx5_B8RBL_acc Q (f x) -> hrx5_B8RBL_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hrx5_B8RBL_acc_l, H | apply hrx5_B8RBL_acc_r, IH, Hin].
Qed.

Lemma hrx5_B8RBL_acc_trans Q B P : hrx5_B8RBL_acc Q B -> hrx5_B8RBL_acc B P -> hrx5_B8RBL_acc Q P.
Proof.
  unfold hrx5_B8RBL_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8RBL_peers PS a sh P Q : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a Q) = peer_rep sh a Q * peers_rep (sdel PS a).
Proof.
  induction PS as [| [[x sh0] w] PS IH]; simpl; intros Hf; [discriminate |].
  unfold peers_rep in *. destruct (EqDec_val x a) as [Ex | Hne]; [subst x |].
  - inversion Hf; subst. simpl. reflexivity.
  - simpl. rewrite IH by exact Hf. unfold peer_item_rep.
    rewrite <- !sepcon_assoc, (sepcon_comm (peer_rep sh0 x w)). reflexivity.
Qed.

Definition hrx5_B8RBL_nv (N: hnode4) (nx: val) : @reptype CKS t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

(* the node N of the list, given an accessor of its value Q *)
Lemma hrx5_B8RBL_nodes_acc (Q: mpred) N : forall NS l, In N NS ->
  (forall nx, hrx5_B8RBL_acc Q (@data_at CKS Ews t_hnode4 (hrx5_B8RBL_nv N nx) (hn_addr N))) ->
  hrx5_B8RBL_acc Q (hnodes_rep4 W l NS).
Proof.
  induction NS as [|N0 NS IH]; intros l Hin HQ; [destruct Hin|]. cbn [hnodes_rep4].
  apply hrx5_B8RBL_acc_prop; intros Hl. apply hrx5_B8RBL_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hrx5_B8RBL_acc_l, hrx5_B8RBL_acc_l, hrx5_B8RBL_acc_r. apply HQ.
  - apply hrx5_B8RBL_acc_r, IH; auto.
Qed.

Lemma hrx5_B8RBL_nfld_p N nx :
  hrx5_B8RBL_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N))
    (@data_at CKS Ews t_hnode4 (hrx5_B8RBL_nv N nx) (hn_addr N)).
Proof.
  unfold hrx5_B8RBL_acc, hrx5_B8RBL_nv.
  rewrite <- (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_p N) (JMeq_refl _))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) _ (hn_p N) (hn_addr N));
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (hn_p N)). apply derives_refl.
Qed.

(* node field p of a node N of the list *)
Lemma hrx5_B8RBL_node_p N NS l : In N NS ->
  hnodes_rep4 W l NS |--
  @field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N) *
  (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N) -* hnodes_rep4 W l NS).
Proof.
  intros Hin. apply (hrx5_B8RBL_nodes_acc _ N NS l Hin). intros nx. apply hrx5_B8RBL_nfld_p.
Qed.

(* ---- pure ---- *)
Lemma hrx5_B8RBL_sfind (PS: list (val * share * peer)) a sh P :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS -> sfind PS a = Some (sh, P).
Proof.
  induction PS as [| [[x shx] u] PS IH]; simpl; intros Hnd Hin; [contradiction|].
  inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (EqDec_val x a) as [E|E].
  - subst x. destruct Hin as [Hin|Hin]; [inversion Hin; reflexivity|].
    exfalso. apply Hni. apply (in_map peer_addr4) in Hin. exact Hin.
  - destruct Hin as [Hin|Hin]; [inversion Hin; congruence|]. apply IH; auto.
Qed.

Lemma hrx5_B8RBL_snapped_len T NS PS : Zlength NS = Zlength PS -> Zlength (hnodes_snapped4 T NS PS) = Zlength NS.
Proof.
  intros H. unfold hnodes_snapped4. rewrite Zlength_map.
  rewrite !Zlength_correct in *. rewrite combine_length. rewrite Nat.min_l; auto. lia.
Qed.

Lemma hrx5_B8RBL_supd_supd (l: list (val * share * peer)) a v u : supd (supd l a v) a u = supd l a u.
Proof.
  induction l as [|[[x shx] y] l IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - destruct (EqDec_val x a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | rewrite IH; reflexivity].
Qed.
