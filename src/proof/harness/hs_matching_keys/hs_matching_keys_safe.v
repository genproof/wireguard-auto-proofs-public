(* The law hs_matching_keys (harness/hs_matching_keys.c), closed: its program is safe.  The assembly of the
   hs_ laws (hs_asm.hs_harness_safe) applied to the law's piece (hmk_piece.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_matching_keys.
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
Require Import WgNoise.proof.harness.hs_matching_keys.hmk_spec.
Require Import WgNoise.proof.harness.hs_matching_keys.hmk_piece.

Lemma hmk_world_units : Forall (fun cs => cspecs_sub cs W_hmk) hs_unit_cs.
Proof. pose proof world_ok_hs_matching_keys as H. inversion H; assumption. Qed.

Lemma hmk_ext : all_unspecified_OK hmk_prog.
Proof. reflexivity. Qed.

Lemma hmk_check : asm_check_gp W_hmk hmk_prog (hs_lib_ids ++ hmk_ids) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hmk_found : hs_unit_found hmk_prog hmk_unit (QP.prog_main hmk_prog :: hmk_ids).
Proof.
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma hmk_imports x25519 aead_enc aead_dec :
  Forall (hs_import_ok W_hmk hmk_prog x25519 aead_enc aead_dec) (hmk_Il x25519 aead_enc aead_dec W_hmk).
Proof.
  unfold hmk_Il. repeat apply Forall_cons; try apply Forall_nil; unfold hs_import_ok.
  1, 2, 3: left; split; [unfold env_specs_gp, asm_env.env_specs; simpl; tauto | reflexivity].
  all: right; left; unfold prot_G5; simpl; repeat first [left; reflexivity | right].
Qed.

Theorem hs_matching_keys_safe : harness_safe WgNoise.contracts.hs_matching_keys.whole_prog.
Proof.
  apply (hs_harness_safe hmk_prog world_OK_whole_hs_matching_keys W_hmk W_hs_matching_keys_eq
           cbc_hs_matching_keys hmk_ext hmk_world_units hs_lib_found_matching_keys HMK.prog hmk_Gl hmk_ids hmk_Il).
  - intros x; reflexivity.
  - intros x. unfold cc_default_all, hmk_Gl. repeat constructor.
  - exact hmk_check.
  - exact hmk_found.
  - exact hmk_imports.
  - exact hmk_piece.
Qed.
