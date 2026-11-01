(* The law hs_begin_session_state: its own piece, main and the harness's copies of the hs_laws.h helpers
   (new_device, new_peer, new_pair), in the unit hs_unit of its world, with the imports hbs_Il. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require Import WgNoise.proof.harness.hs_common.hs_bodies.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_spec.
Require Import WgNoise.proof.harness.hs_begin_session_state.hsbs_main.

Lemma hbs_cs_sub : cspecs_sub CSh W_hbs.
Proof.
  pose proof world_ok_hs_begin_session_state as H. inversion H as [| ? ? _ H1]. inversion H1. assumption.
Qed.

(* the helpers' varspecs are the program's, and none is a function of the unit's context *)
Lemma hbs_Vsub_h x25519 aead_enc aead_dec :
  hc3_lift.hc3_Vsub hs_Vh (QPvarspecs hbs_prog) (hbs_Gmain x25519 aead_enc aead_dec).
Proof.
  unfold hc3_lift.hc3_Vsub, hs_Vh.
  apply Forall_forall. intros [i t] Hin.
  pose proof Hin as Hin'. vm_compute in Hin'.
  repeat destruct Hin' as [Hin' | Hin']; try contradiction; inv Hin'; split; vm_compute; reflexivity.
Qed.

(* the helpers' bodies (hs_lift.v, callees only), lifted into the law's unit *)
Lemma hbs_helpers_ok x25519 aead_enc aead_dec :
  hs_helpers_ok x25519 ->
  Forall (fun ip => verified_in hbs_unit (hbs_Gmain x25519 aead_enc aead_dec) ip) (hbs_Gl x25519).
Proof.
  intros (_ & _ & _ & B4 & B5 & B6 & _ & _).
  unfold hbs_Gl. repeat apply Forall_cons; try apply Forall_nil.
  - eapply hs_helper_entry.
    + exact hbs_cs_sub.
    + exact B4.
    + vm_compute; reflexivity.
    + vm_compute; repeat constructor.
    + hs_gsub.
    + apply hbs_Vsub_h.
  - eapply hs_helper_entry;
      [exact hbs_cs_sub | exact B5 | vm_compute; reflexivity | vm_compute; repeat constructor | hs_gsub | apply hbs_Vsub_h].
  - eapply hs_helper_entry;
      [exact hbs_cs_sub | exact B6 | vm_compute; reflexivity | vm_compute; repeat constructor | hs_gsub | apply hbs_Vsub_h].
Qed.

(* the piece, given the helpers' bodies *)
Lemma hbs_piece_of_helpers x25519 aead_enc aead_dec :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> hs_helpers_ok x25519 ->
  piece_ok [hbs_unit] (hbs_Il x25519 aead_enc aead_dec) (hs_main_spec hbs_prog :: hbs_Gl x25519).
Proof.
  intros Hx Ha Hh. split.
  - vm_compute. repeat constructor; simpl; intuition discriminate.
  - constructor.
    + exists hbs_unit. split; [left; reflexivity |].
      exists HBS.f_main. split; [reflexivity |]. apply (hbs_main_body x25519 aead_enc aead_dec); assumption.
    + eapply Forall_impl; [| apply (hbs_helpers_ok x25519 aead_enc aead_dec Hh)].
      intros ip Hip. exists hbs_unit. split; [left; reflexivity | exact Hip].
Qed.

Theorem hbs_piece x25519 aead_enc aead_dec :
  x25519_props x25519 -> x25519_clamp_inv x25519 -> x25519_dh_agree x25519 -> aead_props aead_enc aead_dec ->
  piece_ok [hbs_unit] (hbs_Il x25519 aead_enc aead_dec) (hs_main_spec hbs_prog :: hbs_Gl x25519).
Proof.
  intros Hx _ _ Ha. exact (hbs_piece_of_helpers x25519 aead_enc aead_dec Hx Ha (hs_common_bodies x25519 Hx)).
Qed.
