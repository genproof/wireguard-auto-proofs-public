(* The shared units' functions and global variables in each hs_ program (hs_asm.hs_lib_found): every function
   of the libc, BLAKE2s, AEAD, Curve25519 and protocol pieces is the same Clight in the program as in its unit,
   and the units' global variables are the program's.  Checked by computation, once per program. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require WgNoise.contracts.hs_begin_session_state WgNoise.contracts.hs_matching_keys
        WgNoise.contracts.hs_reject_initiation WgNoise.contracts.hs_reject_response
        WgNoise.contracts.hs_replay_initiation WgNoise.contracts.hs_response_state
        WgNoise.contracts.hs_session_erases WgNoise.contracts.hs_stale_response.

Ltac hs_found_one :=
  intros i f Hi Hf; vm_compute in Hi; repeat destruct Hi as [<-|Hi]; try contradiction;
  vm_compute in Hf; inv Hf; (split; [vm_compute; reflexivity | repeat constructor]).

Ltac hs_vars_one :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac hs_found_tac :=
  unfold hs_lib_found, hs_lib_units; split; [vm_compute; reflexivity |]; cbn [map app];
  repeat (apply Forall_cons; [split; [hs_found_one | hs_vars_one] |]); apply Forall_nil.

Lemma hs_lib_found_begin_session_state : hs_lib_found WgNoise.contracts.hs_begin_session_state.whole_prog.
Proof. hs_found_tac. Qed.

Lemma hs_lib_found_matching_keys : hs_lib_found WgNoise.contracts.hs_matching_keys.whole_prog.
Proof. hs_found_tac. Qed.

Lemma hs_lib_found_reject_initiation : hs_lib_found WgNoise.contracts.hs_reject_initiation.whole_prog.
Proof. hs_found_tac. Qed.

Lemma hs_lib_found_reject_response : hs_lib_found WgNoise.contracts.hs_reject_response.whole_prog.
Proof. hs_found_tac. Qed.

Lemma hs_lib_found_replay_initiation : hs_lib_found WgNoise.contracts.hs_replay_initiation.whole_prog.
Proof. hs_found_tac. Qed.

Lemma hs_lib_found_response_state : hs_lib_found WgNoise.contracts.hs_response_state.whole_prog.
Proof. hs_found_tac. Qed.

Lemma hs_lib_found_session_erases : hs_lib_found WgNoise.contracts.hs_session_erases.whole_prog.
Proof. hs_found_tac. Qed.

Lemma hs_lib_found_stale_response : hs_lib_found WgNoise.contracts.hs_stale_response.whole_prog.
Proof. hs_found_tac. Qed.
