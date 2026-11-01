(* The law hs_session_erases (harness/hs_session_erases.c), closed: its program is safe.  The assembly of the
   hs_ laws (hs_asm.hs_harness_safe) applied to the law's piece (hse_piece.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_session_erases.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_progs.
Require Import WgNoise.proof.harness.hs_session_erases.hse_statics.
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require Import WgNoise.proof.harness.hs_common.hs_bodies.
Require Import WgNoise.proof.harness.hs_session_erases.hse_piece.

Lemma hse_world_units : Forall (fun cs => cspecs_sub cs W_hse) hs_unit_cs.
Proof. pose proof world_ok_hs_session_erases as H. inversion H; assumption. Qed.

Lemma hse_ext : all_unspecified_OK hse_prog.
Proof. reflexivity. Qed.

Lemma hse_check : asm_check_gp W_hse hse_prog (hs_lib_ids ++ hse_ids) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hse_found : hs_unit_found hse_prog hse_unit (QP.prog_main hse_prog :: hse_ids).
Proof.
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma hse_imports x25519 aead_enc aead_dec :
  Forall (hs_import_ok W_hse hse_prog x25519 aead_enc aead_dec) (hse_Il x25519 aead_enc aead_dec W_hse).
Proof.
  unfold hse_Il. repeat apply Forall_cons; try apply Forall_nil; unfold hs_import_ok.
  1, 2, 3: left; split; [unfold env_specs_gp, asm_env.env_specs; simpl; tauto | reflexivity].
  all: right; left; unfold prot_G5; simpl; repeat first [left; reflexivity | right].
Qed.

Theorem hs_session_erases_safe : harness_safe WgNoise.contracts.hs_session_erases.whole_prog.
Proof.
  apply (hs_harness_safe hse_prog world_OK_whole_hs_session_erases W_hse W_hs_session_erases_eq
           cbc_hs_session_erases hse_ext hse_world_units hs_lib_found_session_erases C.prog hse_Gl hse_ids hse_Il).
  - intros x; reflexivity.
  - intros x. unfold cc_default_all, hse_Gl. repeat constructor.
  - exact hse_check.
  - exact hse_found.
  - exact hse_imports.
  - intros x enc dec Hx _ _ _. exact (hse_piece_of_helpers x enc dec (hs_common_bodies x Hx)).
Qed.
