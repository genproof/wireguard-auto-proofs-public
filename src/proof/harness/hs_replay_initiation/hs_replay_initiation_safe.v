(* The law hs_replay_initiation (harness/hs_replay_initiation.c), closed: its program is safe. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_replay_initiation.
Require Import VST.floyd.VSU.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_progs.
Require Import WgNoise.proof.harness.hs_replay_initiation.hri_main.
Require Import WgNoise.proof.harness.hs_replay_initiation.hri_piece.

(* the program's unspecified globals are allowed (QuickProof.Link) *)
Lemma hri_ext : all_unspecified_OK WgNoise.contracts.hs_replay_initiation.whole_prog.
Proof. reflexivity. Qed.

Theorem hs_replay_initiation_safe : harness_safe WgNoise.contracts.hs_replay_initiation.whole_prog.
Proof.
  apply (hs_harness_safe WgNoise.contracts.hs_replay_initiation.whole_prog world_OK_whole_hs_replay_initiation
           W_hs_replay_initiation W_hs_replay_initiation_eq cbc_hs_replay_initiation hri_ext
           (Forall_inv_tail world_ok_hs_replay_initiation) hs_lib_found_replay_initiation HR.prog hri_Gl
           [HR._any_u64; HR._any_clocks; HR._new_device; HR._new_peer; HR._new_pair] hri_Il).
  - (* the identifiers of the law's statics *)
    intros x. unfold hri_Gl, any_u64_spec, any_clocks_spec, new_device_spec, new_peer_spec, new_pair_spec.
    cbn [map fst]. reflexivity.
  - intros x. unfold WgNoise.proof.common.wg3_iface2.cc_default_all.
    unfold hri_Gl, any_u64_spec, any_clocks_spec, new_device_spec, new_peer_spec, new_pair_spec. repeat constructor.
  - (* asm_assert's checks on the program *)
    vm_compute. reflexivity.
  - (* main and the statics are the program's functions, their locals complete *)
    intros i f Hi Hf. simpl in Hi. repeat destruct Hi as [Hi|Hi]; try contradiction; subst i;
      vm_compute in Hf; inversion Hf; subst f; (split; [vm_compute; reflexivity | repeat constructor]).
  - (* the imports: the environment's nondet_u8 / nondet_u32 / nondet_bytes / gp_assert, and prot_G5 *)
    intros x enc dec. unfold hri_Il.
    apply Forall_app; split; [|apply Forall_forall; intros ix Hix; right; left; exact Hix].
    repeat (apply Forall_cons;
      [left; split; [unfold env_specs_gp, asm_env.env_specs; cbn [In app]; tauto | vm_compute; reflexivity]|]).
    apply Forall_nil.
  - intros x enc dec Hx _ _ _. apply hri_piece_ok; exact Hx.
Qed.
