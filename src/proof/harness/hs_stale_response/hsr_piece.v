(* The law hs_stale_response: its piece, main and the helpers of hs_laws.h main reaches, in the law's unit
   (hs_asm.hs_unit: the world W_hs_stale_response, the whole program's varspecs, the harness's Clight).

   Imports (hs_asm.hs_import_ok): gp_assert, gp_assume, nondet_u32, nondet_bytes of the environment; noise.c's
   wg_noise_init, set_static_identity_private_key, handshake_init (called by the helpers) and the four
   handshake steps main calls.  main's body (hsr_main.v) was proved with its callees only and is lifted here
   (hc3_lift). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise.
Require WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.common.hc3_xcs.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_progs.
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require Import WgNoise.proof.harness.hs_stale_response.hsr_main.
Require WgNoise.contracts.hs_stale_response.
Require WgNoise.harness.hs_stale_response.code.

Definition hsr_p := WgNoise.contracts.hs_stale_response.whole_prog.
Definition hsr_unit : unit_ctx := hs_unit W_hs_stale_response hsr_p WgNoise.harness.hs_stale_response.code.prog.

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the imports, at the compspecs cs of the unit *)
Definition hsr_Il (cs: compspecs) : funspecs :=
  [gp_assert_spec; gp_assume_spec; nondet_u32_spec; @asm_env.nondet_bytes_spec cs;
   wg_noise_init_spec; wg_noise_set_static_identity_private_key_spec x25519; wg_noise_handshake_init_spec x25519;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec;
   wg_noise_handshake_create_response_spec x25519 aead_enc;
   wg_noise_handshake_consume_response_spec x25519 aead_dec].

(* the harness's statics other than main that main reaches *)
Definition hsr_Gl : funspecs :=
  [any_u64_spec; any_clocks_spec; new_device_spec x25519; new_peer_spec x25519; new_pair_spec x25519].

Definition hsr_G : funspecs := hsr_Il W_hs_stale_response ++ hs_main_spec hsr_p :: hsr_Gl.

Lemma hsr_main_entry : verified_in hsr_unit hsr_G (hs_main_spec hsr_p).
Proof.
  eapply (hc3_lift hsr_unit W_hs_stale_response _ _ _ _ _ (hsr_main_body x25519 aead_enc aead_dec)).
  - reflexivity.
  - apply cspecs_sub_refl.
  - vm_compute. repeat constructor.
  - unfold hc3_Gsub, hsr_Gmain.
    repeat (apply Forall_cons; [eexists; split; [reflexivity | apply funspec_sub_refl] |]). apply Forall_nil.
  - unfold hc3_Vsub. cbn [u_V hsr_unit hs_unit]. unfold hsr_p.
    set (V := QPvarspecs _). let x := eval vm_compute in V in change V with x.
    repeat (apply Forall_cons; [split; reflexivity |]). apply Forall_nil.
Qed.

(* the helpers' compspecs CSh is included in the law's world *)
Lemma hsr_cs : cspecs_sub CSh W_hs_stale_response.
Proof.
  pose proof world_ok_hs_stale_response as X. inversion X as [| ? ? _ X1]; subst.
  inversion X1; subst; assumption.
Qed.

(* the helpers' varspecs are the program's and are not functions of the law's context (both varspecs computed
   first: a vm_compute of a goal that still mentions the whole program is far too costly) *)
Lemma hsr_vsub : hc3_Vsub hs_Vh (QPvarspecs hsr_p) hsr_G.
Proof.
  unfold hc3_Vsub, hs_Vh, hsr_p.
  set (V0 := QPvarspecs _). let x := eval vm_compute in V0 in change V0 with x.
  set (V := QPvarspecs _). let x := eval vm_compute in V in change V with x.
  repeat (apply Forall_cons; [split; reflexivity |]). apply Forall_nil.
Qed.

Ltac hsr_entry B :=
  apply (hs_helper_entry W_hs_stale_response hsr_p WgNoise.harness.hs_stale_response.code.prog _ hsr_G _ _ _ hsr_cs B);
  [reflexivity | vm_compute; repeat constructor | hs_gsub | exact hsr_vsub].

(* the law's piece, from the helpers' bodies proved with their callees only *)
Lemma hsr_piece_of_helpers : hs_helpers_ok x25519 -> piece_ok [hsr_unit] hsr_Il (hs_main_spec hsr_p :: hsr_Gl).
Proof.
  intros (B1 & _ & B2 & B3 & B4 & B5 & _). split.
  - apply compute_list_norepet_e. reflexivity.
  - apply Forall_cons; [exists hsr_unit; split; [left; reflexivity | apply hsr_main_entry] |].
    repeat (apply Forall_cons; [exists hsr_unit; split; [left; reflexivity |] |]); [| | | | | apply Forall_nil].
    + hsr_entry B1.
    + hsr_entry B2.
    + hsr_entry B3.
    + hsr_entry B4.
    + hsr_entry B5.
Qed.

End Piece.

(* The law, from the helpers' bodies: the assembly of the hs_ laws (hs_asm.hs_harness_safe) with the piece above *)
Lemma hsr_safe_of_helpers : (forall x25519, x25519_props x25519 -> hs_helpers_ok x25519) -> harness_safe hsr_p.
Proof.
  intros HB.
  apply (hs_harness_safe hsr_p world_OK_whole_hs_stale_response W_hs_stale_response W_hs_stale_response_eq
           cbc_hs_stale_response)
    with (prog := WgNoise.harness.hs_stale_response.code.prog) (Gl := hsr_Gl)
         (ids_l := map fst (hsr_Gl (fun _ _ => nil))) (Il := hsr_Il).
  - reflexivity.
  - pose proof world_ok_hs_stale_response as X. inversion X; subst; assumption.
  - apply hs_lib_found_stale_response.
  - intros x. unfold hsr_Gl, any_u64_spec, any_clocks_spec, new_device_spec, new_peer_spec, new_pair_spec.
    cbn [map fst]. reflexivity.
  - intros x. repeat constructor.
  - vm_compute. reflexivity.
  - intros i f Hi. cbn in Hi.
    repeat destruct Hi as [Hi|Hi]; try contradiction; subst i;
      intros E; vm_compute in E; inversion E; subst f; clear E;
      (split; [vm_compute; reflexivity | cbn; repeat (apply Forall_cons; [reflexivity |]); apply Forall_nil]).
  - intros x enc dec. unfold hsr_Il.
    repeat apply Forall_cons; try apply Forall_nil;
      first [ left; split; [cbn; repeat first [left; reflexivity | right] | vm_compute; reflexivity]
            | right; left; cbn; repeat first [left; reflexivity | right] ].
  - intros x enc dec Hx _ _ _. apply hsr_piece_of_helpers, HB, Hx.
Qed.
