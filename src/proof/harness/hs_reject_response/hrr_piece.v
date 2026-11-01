(* Law hs_reject_response: its own piece.  The harness unit (hs_asm.hs_unit) holds main and the copies of the
   hs_laws.h / hs_unchanged.h helpers (any_u64, bytes_eq, any_clocks, new_device, new_peer, new_pair, copy_peer,
   same_peer: specifications of hs_specs.v).  main's body is proved at the law's world (hrr_main.v); the helpers'
   bodies are proved in the compspecs CSh (hs_bodies.v) and moved into the world with hc3_lift (the harness's
   copies are the same Clight functions).  The imports (hrr_spec.v): the environment's nondet_u8, nondet_u32,
   nondet_bytes and gp_assert, and noise.c's functions that main and the helpers call. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.common.hc3_xcs.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_bodies.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_spec.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_main.

Definition hrr_ids : list ident := ltac:(let l := eval compute in (map fst (hrr_Gl (fun _ _ => nil))) in exact l).

(* the harness unit *)
Definition hrr_unit : unit_ctx := hs_unit W_hs_reject_response p_rr R.prog.

Lemma hrr_cs_sub : cspecs_sub CSh W_hs_reject_response.
Proof. pose proof world_ok_hs_reject_response as H. inversion H as [|? ? _ HT]. inversion HT; assumption. Qed.

(* a helper's body proved in CSh with the context G0, V0 (each entry of G0 in the piece's context) *)
Lemma hrr_lift x25519 aead_enc aead_dec V0 G0 f ip :
  @semax_body V0 G0 CSh f ip ->
  find_internal R.prog (fst ip) = Some f ->
  Forall (fun it => complete_type (@cenv_cs CSh) (snd it) = true) (fn_vars f) ->
  hc3_Gsub G0 (hrr_G x25519 aead_enc aead_dec) ->
  hc3_Vsub V0 (QPvarspecs p_rr) (hrr_G x25519 aead_enc aead_dec) ->
  verified_in hrr_unit (hrr_Il x25519 aead_enc aead_dec (u_cs hrr_unit) ++ hs_main_spec p_rr :: hrr_Gl x25519) ip.
Proof.
  intros B F C HG HV. eapply hc3_lift; [exact B | exact F | exact hrr_cs_sub | exact C | exact HG | exact HV].
Qed.

Ltac hrr_Gsub :=
  unfold hc3_Gsub;
  repeat (apply Forall_cons;
          [cbv beta; eexists; split; [reflexivity | first [apply funspec_sub_refl | apply hc3_nondet_bytes_xcs]] |]);
  apply Forall_nil.

Ltac hrr_Vsub :=
  match goal with |- hc3_Vsub ?V _ _ => let v := eval vm_compute in V in change V with v end;
  unfold hc3_Vsub; repeat (apply Forall_cons; [split; reflexivity |]); apply Forall_nil.

Theorem hrr_piece x25519 aead_enc aead_dec :
  x25519_props x25519 -> x25519_clamp_inv x25519 -> x25519_dh_agree x25519 -> aead_props aead_enc aead_dec ->
  piece_ok [hrr_unit] (hrr_Il x25519 aead_enc aead_dec) (hs_main_spec p_rr :: hrr_Gl x25519).
Proof.
  intros HX _ _ _. split.
  - vm_compute. repeat constructor; simpl; intuition discriminate.
  - destruct (hs_common_bodies x25519 HX) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    unfold hrr_Gl.
    repeat apply Forall_cons; try apply Forall_nil; exists hrr_unit; (split; [left; reflexivity |]).
    + exists R.f_main. split; [reflexivity |]. exact (hrr_main_body x25519 aead_enc aead_dec).
    + refine (hrr_lift x25519 aead_enc aead_dec _ _ _ _ B1 _ _ _ _); [reflexivity | repeat constructor | hrr_Gsub | hrr_Vsub].
    + refine (hrr_lift x25519 aead_enc aead_dec _ _ _ _ B2 _ _ _ _); [reflexivity | repeat constructor | hrr_Gsub | hrr_Vsub].
    + refine (hrr_lift x25519 aead_enc aead_dec _ _ _ _ B3 _ _ _ _); [reflexivity | repeat constructor | hrr_Gsub | hrr_Vsub].
    + refine (hrr_lift x25519 aead_enc aead_dec _ _ _ _ B4 _ _ _ _); [reflexivity | repeat constructor | hrr_Gsub | hrr_Vsub].
    + refine (hrr_lift x25519 aead_enc aead_dec _ _ _ _ B5 _ _ _ _); [reflexivity | repeat constructor | hrr_Gsub | hrr_Vsub].
    + refine (hrr_lift x25519 aead_enc aead_dec _ _ _ _ B6 _ _ _ _); [reflexivity | repeat constructor | hrr_Gsub | hrr_Vsub].
    + refine (hrr_lift x25519 aead_enc aead_dec _ _ _ _ B7 _ _ _ _); [reflexivity | repeat constructor | hrr_Gsub | hrr_Vsub].
    + refine (hrr_lift x25519 aead_enc aead_dec _ _ _ _ B8 _ _ _ _); [reflexivity | repeat constructor | hrr_Gsub | hrr_Vsub].
Qed.
