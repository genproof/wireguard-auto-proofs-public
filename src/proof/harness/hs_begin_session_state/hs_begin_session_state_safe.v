(* The law hs_begin_session_state (harness/hs_begin_session_state.c), closed: its program is safe.  The assembly of
   the hs_ laws (hs_asm.hs_harness_safe) applied to the law's piece (hsbs_piece.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_begin_session_state.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_progs.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_spec.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_piece.

Theorem hs_begin_session_state_safe : harness_safe WgNoise.contracts.hs_begin_session_state.whole_prog.
Proof.
  apply (hs_harness_safe hbs_prog world_OK_whole_hs_begin_session_state W_hbs W_hs_begin_session_state_eq
           cbc_hs_begin_session_state ltac:(reflexivity) (Forall_inv_tail world_ok_hs_begin_session_state)
           hs_lib_found_begin_session_state HBS.prog hbs_Gl [HBS._new_device; HBS._new_peer; HBS._new_pair] hbs_Il).
  - (* the identifiers of the law's statics *)
    intros x. unfold hbs_Gl, new_device_spec, new_peer_spec, new_pair_spec. cbn [map fst]. reflexivity.
  - intros x. unfold WgNoise.proof.common.wg3_iface2.cc_default_all.
    unfold hbs_Gl, new_device_spec, new_peer_spec, new_pair_spec. repeat constructor.
  - (* asm_assert's checks on the program *)
    vm_compute. reflexivity.
  - (* main and the statics are the program's functions, their locals complete *)
    intros i f Hi Hf. simpl in Hi. repeat destruct Hi as [Hi|Hi]; try contradiction; subst i;
      vm_compute in Hf; inversion Hf; subst f; (split; [vm_compute; reflexivity | repeat constructor]).
  - (* the imports: the environment's nondet_u8 / nondet_u32 / nondet_bytes / gp_assert, and prot_G5's *)
    intros x enc dec. unfold hbs_Il.
    repeat apply Forall_cons; try apply Forall_nil; unfold hs_import_ok.
    1-4: left; split; [unfold env_specs_gp, asm_env.env_specs; cbn [In app]; tauto | vm_compute; reflexivity].
    all: right; left; unfold prot_G5; simpl; repeat first [left; reflexivity | right].
  - exact hbs_piece.
Qed.
