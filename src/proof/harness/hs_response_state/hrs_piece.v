(* The law hs_response_state: its own piece, main and the harness's copies of the hs_laws.h helpers main reaches
   (any_u64, any_clocks, new_device, new_peer, new_pair), in the law's unit hrs_unit.  Its imports are main's
   (hrs_Il) and the functions of noise.c and of the environment the helpers call.  main's body (hrs_main.v) and
   the helpers' bodies (hs_lift.hs_helpers_ok, each with its callees only) are lifted into the piece's context
   (hc3_lift). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.common.hc3_xcs.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require Import WgNoise.proof.harness.hs_response_state.hrs_spec.
Require Import WgNoise.proof.harness.hs_response_state.hrs_main.

(* the piece's imports: main's, and the callees of the helpers outside the harness *)
Definition hrs_Ip (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (cs: compspecs) : funspecs :=
  hrs_Il x25519 aead_enc aead_dec cs ++
  [@asm_env.nondet_bytes_spec cs; wg_noise_init_spec; wg_noise_set_static_identity_private_key_spec x25519;
   wg_noise_handshake_init_spec x25519].

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

Definition hrs_G : funspecs := hrs_Ip x25519 aead_enc aead_dec W_hrs ++ hs_main_spec hrs_prog :: hrs_Gl x25519.

Lemma hrs_world_CSh : cspecs_sub CSh W_hrs.
Proof.
  pose proof world_ok_hs_response_state as X. inversion X as [| ? ? _ X1]; subst.
  inversion X1; subst; assumption.
Qed.

Lemma hrs_main_entry : x25519_props x25519 -> aead_props aead_enc aead_dec ->
  verified_in hrs_unit hrs_G (hs_main_spec hrs_prog).
Proof.
  intros Hx Ha.
  eapply (hc3_lift hrs_unit W_hrs _ _ _ _ _ (hrs_main_body x25519 aead_enc aead_dec Hx Ha)).
  - reflexivity.
  - apply cspecs_sub_refl.
  - vm_compute. repeat constructor.
  - unfold hc3_Gsub, hrs_Gmain, hrs_Il, hrs_Gl.
    repeat (apply Forall_cons; [eexists; split; [reflexivity | apply funspec_sub_refl] |]). apply Forall_nil.
  - unfold hc3_Vsub. cbn [u_V hrs_unit hs_unit].
    set (V := QPvarspecs _). let x := eval vm_compute in V in change V with x.
    repeat (apply Forall_cons; [split; reflexivity |]). apply Forall_nil.
Qed.

Ltac hrs_entry B :=
  apply (hs_helper_entry _ _ _ _ _ _ _ _ hrs_world_CSh B); [reflexivity | vm_compute; repeat constructor | hs_gsub | hs_vsub].

Lemma hrs_piece_of_helpers : x25519_props x25519 -> aead_props aead_enc aead_dec -> hs_helpers_ok x25519 ->
  piece_ok [hrs_unit] (hrs_Ip x25519 aead_enc aead_dec) (hs_main_spec hrs_prog :: hrs_Gl x25519).
Proof.
  intros Hx Ha (B1 & _ & B3 & B4 & B5 & B6 & _). split.
  - apply compute_list_norepet_e. reflexivity.
  - apply Forall_cons; [exists hrs_unit; split; [left; reflexivity | apply hrs_main_entry; assumption] |].
    repeat (apply Forall_cons; [exists hrs_unit; split; [left; reflexivity |] |]); [| | | | | apply Forall_nil].
    + hrs_entry B1.
    + hrs_entry B3.
    + hrs_entry B4.
    + hrs_entry B5.
    + hrs_entry B6.
Qed.

End Piece.
