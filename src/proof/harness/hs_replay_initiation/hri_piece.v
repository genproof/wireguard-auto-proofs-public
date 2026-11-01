(* law hs_replay_initiation: the law's own piece (main and the harness's copies of the hs_laws.h helpers it
   reaches), in the unit hs_unit of its world, with the imports hri_Il (hri_main.v). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require Import WgNoise.proof.harness.hs_common.hs_bodies.
Require Import WgNoise.proof.harness.hs_replay_initiation.hri_main.
Require WgNoise.contracts.hs_replay_initiation.
Require WgNoise.harness.hs_replay_initiation.code.

Definition hri_unit : unit_ctx := hs_unit W_hs_replay_initiation hri_prog HR.prog.

(* the helpers' global variables (the shim's clocks) are the program's, and are not functions of the context
   (both varspecs computed first: vm_compute on the whole goal is far too costly) *)
Lemma hri_vsub x25519 aead_enc aead_dec : hc3_Vsub hs_Vh (QPvarspecs hri_prog) (hri_G x25519 aead_enc aead_dec).
Proof.
  unfold hc3_Vsub, hs_Vh, hri_prog.
  set (V0 := QPvarspecs _). let x := eval vm_compute in V0 in change V0 with x.
  set (V := QPvarspecs _). let x := eval vm_compute in V in change V with x.
  repeat (apply Forall_cons; [split; reflexivity |]). apply Forall_nil.
Qed.

(* the helpers' bodies (hs_bodies.v, each with its callees only), lifted into the law's unit: their callees are
   among main's imports (nondet_u32, nondet_bytes, noise.c's) and the law's helpers *)
Lemma hri_helpers_ok x25519 aead_enc aead_dec :
  x25519_props x25519 ->
  Forall (fun ip => verified_in hri_unit (hri_G x25519 aead_enc aead_dec) ip) (hri_Gl x25519).
Proof.
  intros Hx. destruct (hs_common_bodies x25519 Hx) as (B1 & _ & B3 & B4 & B5 & B6 & _).
  assert (CS: cspecs_sub CSh W_hs_replay_initiation)
    by exact (Forall_inv (Forall_inv_tail world_ok_hs_replay_initiation)).
  unfold hri_Gl.
  repeat apply Forall_cons; try apply Forall_nil.
  - eapply hs_helper_entry; [exact CS | exact B1 | vm_compute; reflexivity | vm_compute; repeat constructor | hs_gsub | apply hri_vsub].
  - eapply hs_helper_entry; [exact CS | exact B3 | vm_compute; reflexivity | vm_compute; repeat constructor | hs_gsub | apply hri_vsub].
  - eapply hs_helper_entry; [exact CS | exact B4 | vm_compute; reflexivity | vm_compute; repeat constructor | hs_gsub | apply hri_vsub].
  - eapply hs_helper_entry; [exact CS | exact B5 | vm_compute; reflexivity | vm_compute; repeat constructor | hs_gsub | apply hri_vsub].
  - eapply hs_helper_entry; [exact CS | exact B6 | vm_compute; reflexivity | vm_compute; repeat constructor | hs_gsub | apply hri_vsub].
Qed.

Lemma hri_piece_ok x25519 aead_enc aead_dec :
  x25519_props x25519 ->
  piece_ok [hri_unit] (hri_Il x25519 aead_enc aead_dec) (hs_main_spec hri_prog :: hri_Gl x25519).
Proof.
  intros Hx. split.
  - vm_compute. repeat constructor; simpl; intuition discriminate.
  - constructor.
    + exists hri_unit. split; [left; reflexivity|].
      exists HR.f_main. split; [reflexivity|]. apply hri_main_body.
    + eapply Forall_impl; [|apply (hri_helpers_ok x25519 aead_enc aead_dec Hx)].
      intros ip Hip. exists hri_unit. split; [left; reflexivity | exact Hip].
Qed.
