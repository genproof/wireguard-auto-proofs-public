(* The law hs_reject_initiation (harness/hs_reject_initiation.c), closed: its program is safe.  The assembly of the
   hs_ laws (hs_asm.hs_harness_safe) applied to the law's piece (hri_piece.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_reject_initiation.
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
Require Import WgNoise.proof.harness.hs_reject_initiation.hri_piece.

Lemma hri_world_units : Forall (fun cs => cspecs_sub cs W_hri) hs_unit_cs.
Proof. pose proof world_ok_hs_reject_initiation as H. inversion H; assumption. Qed.

Lemma hri_ext : all_unspecified_OK hri_prog.
Proof. reflexivity. Qed.

Lemma hri_check : asm_check_gp W_hri hri_prog (hs_lib_ids ++ hri_ids) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hri_found : hs_unit_found hri_prog hri_unit (QP.prog_main hri_prog :: hri_ids).
Proof.
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma hri_imports x25519 aead_enc aead_dec :
  Forall (hs_import_ok W_hri hri_prog x25519 aead_enc aead_dec) (hri_Il x25519 aead_enc aead_dec W_hri).
Proof.
  unfold hri_Il. repeat apply Forall_cons; try apply Forall_nil; unfold hs_import_ok.
  1-4: left; split; [unfold env_specs_gp, asm_env.env_specs; simpl; tauto | reflexivity].
  all: right; left; unfold prot_G5; simpl; repeat first [left; reflexivity | right].
Qed.

Theorem hs_reject_initiation_safe : harness_safe WgNoise.contracts.hs_reject_initiation.whole_prog.
Proof.
  apply (hs_harness_safe hri_prog world_OK_whole_hs_reject_initiation W_hri W_hs_reject_initiation_eq
           cbc_hs_reject_initiation hri_ext hri_world_units hs_lib_found_reject_initiation H.prog hri_Gl hri_ids hri_Il).
  - intros x; reflexivity.
  - intros x. unfold cc_default_all, hri_Gl. repeat constructor.
  - exact hri_check.
  - exact hri_found.
  - exact hri_imports.
  - exact hri_piece.
Qed.
