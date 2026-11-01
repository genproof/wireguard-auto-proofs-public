(* Law hs_reject_initiation: its own piece.  The harness unit (hs_asm.hs_unit) holds main and the copies of the
   hs_laws.h / hs_unchanged.h helpers (any_u64, bytes_eq, any_clocks, new_device, new_peer, new_pair, copy_peer,
   same_peer: specifications of hs_specs.v).  Their bodies are proved in the harness's compspecs CSh (main in
   hri_main.v, the helpers in hs_bodies.v) and moved into the law's world W_hs_reject_initiation with hc3_lift.
   The imports: nondet_u8, nondet_u32, nondet_bytes and gp_assert (the environment), and noise.c's
   wg_noise_init, set_static_identity_private_key, handshake_init (called by the helpers), create_initiation and
   consume_initiation (called by main), at the world compspecs. *)
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
Require Import WgNoise.proof.harness.hs_common.hs_globals.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_reject_initiation.hri_spec.
Require Import WgNoise.proof.harness.hs_reject_initiation.hri_main.
Require WgNoise.contracts.hs_reject_initiation.

Notation hri_prog := WgNoise.contracts.hs_reject_initiation.whole_prog.
Notation W_hri := W_hs_reject_initiation.

(* the harness's static functions other than main *)
Definition hri_Gl (x25519: list byte -> list byte -> list byte) : funspecs :=
  [any_u64_spec; bytes_eq_spec; any_clocks_spec; new_device_spec x25519; new_peer_spec x25519;
   new_pair_spec x25519; copy_peer_spec; same_peer_spec].

Definition hri_ids : list ident := ltac:(let l := eval compute in (map fst (hri_Gl (fun _ _ => nil))) in exact l).

(* the imports of main and the helpers *)
Definition hri_Il (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (cs: compspecs) : funspecs :=
  [nondet_u8_spec; nondet_u32_spec; @asm_env.nondet_bytes_spec cs; gp_assert_spec;
   wg_noise_init_spec; wg_noise_set_static_identity_private_key_spec x25519; wg_noise_handshake_init_spec x25519;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec].

(* the harness unit *)
Definition hri_unit : unit_ctx := hs_unit W_hri hri_prog H.prog.

(* the context of the piece's bodies *)
Definition hri_Gall x25519 aead_enc aead_dec : funspecs :=
  hri_Il x25519 aead_enc aead_dec W_hri ++ hs_main_spec hri_prog :: hri_Gl x25519.

Lemma hri_cs_sub : cspecs_sub CSh W_hri.
Proof. pose proof world_ok_hs_reject_initiation as H. inversion H; assumption. Qed.

(* a body proved in CSh with the context G0, V0 (each entry of G0 in the piece's context) *)
Lemma hri_lift x25519 aead_enc aead_dec V0 G0 f ip :
  @semax_body V0 G0 CSh f ip ->
  find_internal H.prog (fst ip) = Some f ->
  Forall (fun it => complete_type (@cenv_cs CSh) (snd it) = true) (fn_vars f) ->
  hc3_Gsub G0 (hri_Gall x25519 aead_enc aead_dec) ->
  hc3_Vsub V0 (QPvarspecs hri_prog) (hri_Gall x25519 aead_enc aead_dec) ->
  verified_in hri_unit (hri_Il x25519 aead_enc aead_dec (u_cs hri_unit) ++ hs_main_spec hri_prog :: hri_Gl x25519) ip.
Proof.
  intros B F C HG HV. eapply hc3_lift; [exact B | exact F | exact hri_cs_sub | exact C | exact HG | exact HV].
Qed.

Ltac hri_Gsub :=
  unfold hc3_Gsub;
  repeat (apply Forall_cons;
          [cbv beta; eexists; split; [reflexivity | first [apply funspec_sub_refl | apply hc3_nondet_bytes_xcs]] |]);
  apply Forall_nil.

Ltac hri_Vsub :=
  match goal with |- hc3_Vsub ?V _ _ => let v := eval vm_compute in V in change V with v end;
  unfold hc3_Vsub; repeat (apply Forall_cons; [split; reflexivity |]); apply Forall_nil.

Theorem hri_piece x25519 aead_enc aead_dec :
  x25519_props x25519 -> x25519_clamp_inv x25519 -> x25519_dh_agree x25519 -> aead_props aead_enc aead_dec ->
  piece_ok [hri_unit] (hri_Il x25519 aead_enc aead_dec) (hs_main_spec hri_prog :: hri_Gl x25519).
Proof.
  intros HX _ _ _. split.
  - vm_compute. repeat constructor; simpl; intuition discriminate.
  - destruct (hs_common_bodies x25519 HX) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    unfold hri_Gl.
    repeat apply Forall_cons; try apply Forall_nil; exists hri_unit; (split; [left; reflexivity |]).
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _
                (hri_main_body x25519 aead_enc aead_dec hs_shim0 hs_w0 zeros32 zeros32 Int64.zero
                   hs_init_globals_reject_initiation) _ _ _ _);
        [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _ B1 _ _ _ _); [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _ B2 _ _ _ _); [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _ B3 _ _ _ _); [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _ B4 _ _ _ _); [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _ B5 _ _ _ _); [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _ B6 _ _ _ _); [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _ B7 _ _ _ _); [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
    + refine (hri_lift x25519 aead_enc aead_dec _ _ _ _ B8 _ _ _ _); [reflexivity | repeat constructor | hri_Gsub | hri_Vsub].
Qed.
