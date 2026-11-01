(* law consume_response_any, phase Q5, segment A2: separation-logic helpers (the field p of
   one node of hnodes_rep4, as hcr5_P6.v's accessors; the lent objects as vobjs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope Z_scope.

#[local] Instance hcr5_q5_A2_cceK : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.

Section hcr5_q5_A2_helpers.
Local Open Scope logic.

Definition hcr5_q5_A2_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hcr5_q5_A2_acc_l Q A F : hcr5_q5_A2_acc Q A -> hcr5_q5_A2_acc Q (A * F).
Proof.
  unfold hcr5_q5_A2_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hcr5_q5_A2_acc_r Q A F : hcr5_q5_A2_acc Q A -> hcr5_q5_A2_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hcr5_q5_A2_acc_l, H. Qed.

Lemma hcr5_q5_A2_acc_prop Q (c: Prop) A : (c -> hcr5_q5_A2_acc Q A) -> hcr5_q5_A2_acc Q (!! c && A).
Proof.
  unfold hcr5_q5_A2_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcr5_q5_A2_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hcr5_q5_A2_acc Q (A x)) -> hcr5_q5_A2_acc Q (EX x, A x).
Proof.
  unfold hcr5_q5_A2_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

(* the node's field p, at the world *)
Lemma hcr5_q5_A2_node_split p sn r rs nx x :
  @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x |--
  @field_at W Ews t_hnode4 [StructField HC._p] p x *
  (@field_at W Ews t_hnode4 [StructField HC._p] p x -* @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x).
Proof.
  rewrite <- (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HC._p] p p (JMeq_refl p))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  (eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) _ p x); [apply JMeq_refl | auto with field_compatible] |]).
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p).
  apply derives_refl.
Qed.

Lemma hcr5_q5_A2_node_acc l NS N : In N NS ->
  hcr5_q5_A2_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N)) (hnodes_rep4 W l NS).
Proof.
  revert l; induction NS as [|N0 NS IH]; intros l Hin; [destruct Hin|]. cbn [hnodes_rep4].
  apply hcr5_q5_A2_acc_prop; intros Hl. apply hcr5_q5_A2_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hcr5_q5_A2_acc_l, hcr5_q5_A2_acc_l, hcr5_q5_A2_acc_r. apply hcr5_q5_A2_node_split.
  - apply hcr5_q5_A2_acc_r, IH, Hin.
Qed.

Lemma hcr5_q5_A2_hn_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [|N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end.
    apply isptr_is_pointer_or_null; exact Hp.
Qed.

(* the lent objects: B's device and the kents *)
Lemma hcr5_q5_A2_vo sh wg D l KE :
  device_rep sh wg D * kents_rep W l KE = vobjs W [VDev sh wg D; VKents l KE].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

End hcr5_q5_A2_helpers.
