(* The law hs_reject_response (harness/hs_reject_response.c), closed: its program is safe.  The assembly of the
   hs_ laws (hs_asm.hs_harness_safe) applied to the law's piece (hrr_piece.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_reject_response.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_progs.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_spec.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_piece.

Lemma hrr_world_units : Forall (fun cs => cspecs_sub cs W_hs_reject_response) hs_unit_cs.
Proof. pose proof world_ok_hs_reject_response as H. inversion H; assumption. Qed.

Lemma hrr_ext : all_unspecified_OK p_rr.
Proof. reflexivity. Qed.

Lemma hrr_check : asm_check_gp W_hs_reject_response p_rr (hs_lib_ids ++ hrr_ids) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hrr_found : hs_unit_found p_rr hrr_unit (QP.prog_main p_rr :: hrr_ids).
Proof.
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma hrr_imports x25519 aead_enc aead_dec :
  Forall (hs_import_ok W_hs_reject_response p_rr x25519 aead_enc aead_dec)
    (hrr_Il x25519 aead_enc aead_dec W_hs_reject_response).
Proof.
  unfold hrr_Il. repeat apply Forall_cons; try apply Forall_nil; unfold hs_import_ok.
  1-4: left; split; [unfold env_specs_gp, asm_env.env_specs; simpl; tauto | reflexivity].
  all: right; left; unfold prot_G5; simpl; repeat first [left; reflexivity | right].
Qed.

Theorem hs_reject_response_safe : harness_safe WgNoise.contracts.hs_reject_response.whole_prog.
Proof.
  apply (hs_harness_safe p_rr world_OK_whole_hs_reject_response W_hs_reject_response W_hs_reject_response_eq
           cbc_hs_reject_response hrr_ext hrr_world_units hs_lib_found_reject_response R.prog hrr_Gl hrr_ids hrr_Il).
  - intros x; reflexivity.
  - intros x. unfold cc_default_all, hrr_Gl. repeat constructor.
  - exact hrr_check.
  - exact hrr_found.
  - exact hrr_imports.
  - exact hrr_piece.
Qed.
