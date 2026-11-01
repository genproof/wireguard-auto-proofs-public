(* CS4nb is a sub-compspecs of CS4.  Tactic as hc4a_lib.v's hc4a_cssub. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.

Lemma hc4nb2_ke_cs_sub : cspecs_sub CS4nb CS4.
Proof.
  split3; intros ?i; apply sub_option_get; apply Forall_forall; intros ?x ?Hx; vm_compute in Hx;
  repeat destruct Hx as [<-|Hx]; try contradiction; vm_compute; reflexivity.
Qed.

Lemma hc4nb2_ke_cs_sub_w CSw : cspecs_sub CS4 CSw -> cspecs_sub CS4nb CSw.
Proof. intros H. exact (cspecs_sub_trans hc4nb2_ke_cs_sub H). Qed.
