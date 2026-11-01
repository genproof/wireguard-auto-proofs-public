(* The law hs_response_state: the assembly of the hs_ laws (hs_asm.hs_harness_safe) applied to the law's piece
   (hrs_piece.v), given the helpers' bodies (hs_lift.hs_helpers_ok). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_response_state.
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
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require Import WgNoise.proof.harness.hs_response_state.hrs_spec.
Require Import WgNoise.proof.harness.hs_response_state.hrs_piece.

Lemma hrs_world_units : Forall (fun cs => cspecs_sub cs W_hrs) hs_unit_cs.
Proof. pose proof world_ok_hs_response_state as H. inversion H; assumption. Qed.

Lemma hrs_ext : all_unspecified_OK hrs_prog.
Proof. reflexivity. Qed.

Lemma hrs_check : asm_check_gp W_hrs hrs_prog (hs_lib_ids ++ hrs_ids) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hrs_found : hs_unit_found hrs_prog hrs_unit (QP.prog_main hrs_prog :: hrs_ids).
Proof.
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma hrs_imports x25519 aead_enc aead_dec :
  Forall (hs_import_ok W_hrs hrs_prog x25519 aead_enc aead_dec) (hrs_Ip x25519 aead_enc aead_dec W_hrs).
Proof.
  unfold hrs_Ip, hrs_Il. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; unfold hs_import_ok.
  1, 2, 7: left; split; [unfold env_specs_gp, asm_env.env_specs; simpl; tauto | reflexivity].
  all: right; left; unfold prot_G5; simpl; repeat first [left; reflexivity | right].
Qed.

Theorem hrs_safe_of_helpers :
  (forall x25519, x25519_props x25519 -> hs_helpers_ok x25519) ->
  harness_safe WgNoise.contracts.hs_response_state.whole_prog.
Proof.
  intros HH.
  apply (hs_harness_safe hrs_prog world_OK_whole_hs_response_state W_hrs W_hs_response_state_eq
           cbc_hs_response_state hrs_ext hrs_world_units hs_lib_found_response_state HRS.prog hrs_Gl hrs_ids hrs_Ip).
  - intros x; reflexivity.
  - intros x. unfold cc_default_all, hrs_Gl. repeat constructor.
  - exact hrs_check.
  - exact hrs_found.
  - exact hrs_imports.
  - intros x enc dec Hx _ _ Ha. exact (hrs_piece_of_helpers x enc dec Hx Ha (HH x Hx)).
Qed.
