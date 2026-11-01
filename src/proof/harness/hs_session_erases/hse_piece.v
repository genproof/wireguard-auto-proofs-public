(* The law hs_session_erases: its own piece, the functions of the harness unit (hs_asm.hs_unit): main, the
   harness's statics zero and erased, and its copies of the hs_laws.h helpers any_u64, any_clocks, new_device,
   new_peer, new_pair.  Each body is proved in a small context (hse_main.v, hse_statics.v, hs_bodies.v) and
   lifted into the unit with hc3_lift.

   The imports (hse_Il) are the functions the unit calls outside the harness: nondet_u32, nondet_bytes and
   gp_assert (the environment), and noise.c's wg_noise_init, set_static_identity_private_key,
   wg_noise_handshake_init, the four handshake steps and begin_session (protocol v5, at the world's compspecs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require Import WgNoise.proof.harness.hs_session_erases.hse_statics.
Require Import WgNoise.proof.harness.hs_session_erases.hse_main.
Require WgNoise.contracts.hs_session_erases.

Notation hse_prog := WgNoise.contracts.hs_session_erases.whole_prog.
Notation W_hse := W_hs_session_erases.

(* the harness's static functions other than main *)
Definition hse_Gl (x25519: list byte -> list byte -> list byte) : funspecs :=
  [any_u64_spec; any_clocks_spec; new_device_spec x25519; new_peer_spec x25519; new_pair_spec x25519;
   zero_spec; erased_spec].

Definition hse_ids : list ident := ltac:(let l := eval compute in (map fst (hse_Gl (fun _ _ => nil))) in exact l).

(* the unit's imports *)
Definition hse_Il (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (cs: compspecs) : funspecs :=
  [nondet_u32_spec; @asm_env.nondet_bytes_spec cs; gp_assert_spec;
   wg_noise_init_spec; wg_noise_set_static_identity_private_key_spec x25519; wg_noise_handshake_init_spec x25519;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec;
   wg_noise_handshake_create_response_spec x25519 aead_enc;
   wg_noise_handshake_consume_response_spec x25519 aead_dec;
   wg_noise_handshake_begin_session_spec cs].

(* the harness unit and the context of its bodies *)
Definition hse_unit : unit_ctx := hs_unit W_hse hse_prog C.prog.

Definition hse_G (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) : funspecs :=
  hse_Il x25519 aead_enc aead_dec W_hse ++ hs_main_spec hse_prog :: hse_Gl x25519.

Lemma hse_world_harness : cspecs_sub HCS W_hse.
Proof. pose proof world_ok_hs_session_erases as H. inversion H; assumption. Qed.

(* each entry of a small context is, literally, an entry of the unit's context *)
Ltac hse_Gsub :=
  unfold hc3_Gsub; repeat (apply Forall_cons; [cbv beta; eexists; split; [reflexivity | apply funspec_sub_refl] |]);
  apply Forall_nil.

(* the global variables of the bodies' varspecs are the unit's, and none is a function of its context *)
Lemma hse_Vsub x25519 aead_enc aead_dec :
  hc3_Vsub hse_V (u_V hse_unit) (hse_G x25519 aead_enc aead_dec).
Proof.
  unfold hc3_Vsub, hse_unit, hs_unit; simpl u_V. unfold hse_V.
  apply Forall_forall. intros [i t] Hin.
  pose proof Hin as Hin'. vm_compute in Hin'.
  repeat destruct Hin' as [Hin' | Hin']; try contradiction; inv Hin'; split; try reflexivity; vm_compute; reflexivity.
Qed.

(* the bodies of main and of zero and erased, lifted into the unit *)
Lemma hse_piece_own x25519 aead_enc aead_dec :
  Forall (verified_in hse_unit (hse_G x25519 aead_enc aead_dec))
    [hs_main_spec hse_prog; zero_spec; erased_spec].
Proof.
  destruct hse_statics_bodies as [Bz Be].
  repeat apply Forall_cons; try apply Forall_nil.
  - refine (hc3_lift hse_unit HCS hse_V _ C.f_main _ _ (hse_main_body x25519 aead_enc aead_dec) _
              hse_world_harness _ _ (hse_Vsub x25519 aead_enc aead_dec)).
    + vm_compute. reflexivity.
    + repeat constructor.
    + hse_Gsub.
  - refine (hc3_lift hse_unit HCS hse_V _ C.f_zero _ _ Bz _ hse_world_harness _ _
              (hse_Vsub x25519 aead_enc aead_dec)).
    + vm_compute. reflexivity.
    + repeat constructor.
    + hse_Gsub.
  - refine (hc3_lift hse_unit HCS hse_V _ C.f_erased _ _ Be _ hse_world_harness _ _
              (hse_Vsub x25519 aead_enc aead_dec)).
    + vm_compute. reflexivity.
    + repeat constructor.
    + hse_Gsub.
Qed.

(* the helpers' varspecs are the program's, and none is a function of the unit's context *)
Lemma hse_Vsub_h x25519 aead_enc aead_dec :
  hc3_Vsub hs_Vh (QPvarspecs hse_prog) (hse_G x25519 aead_enc aead_dec).
Proof.
  unfold hc3_Vsub, hs_Vh.
  apply Forall_forall. intros [i t] Hin.
  pose proof Hin as Hin'. vm_compute in Hin'.
  repeat destruct Hin' as [Hin' | Hin']; try contradiction; inv Hin'; split; vm_compute; reflexivity.
Qed.

(* the copies of the hs_laws.h helpers, lifted into the unit from their bodies (hs_lift.v) *)
Lemma hse_piece_helpers x25519 aead_enc aead_dec :
  hs_helpers_ok x25519 ->
  Forall (verified_in hse_unit (hse_G x25519 aead_enc aead_dec))
    [any_u64_spec; any_clocks_spec; new_device_spec x25519; new_peer_spec x25519; new_pair_spec x25519].
Proof.
  intros (B1 & _ & B3 & B4 & B5 & B6 & _).
  assert (CS: cspecs_sub CSh W_hse).
  { pose proof world_ok_hs_session_erases as H. inversion H as [| ? ? _ H']; subst. inversion H'; assumption. }
  repeat apply Forall_cons; try apply Forall_nil.
  - refine (hs_helper_entry W_hse hse_prog C.prog _ _ _ _ _ CS B1 _ _ _ _);
      [vm_compute; reflexivity | repeat constructor | hs_gsub | apply hse_Vsub_h].
  - refine (hs_helper_entry W_hse hse_prog C.prog _ _ _ _ _ CS B3 _ _ _ _);
      [vm_compute; reflexivity | repeat constructor | hs_gsub | apply hse_Vsub_h].
  - refine (hs_helper_entry W_hse hse_prog C.prog _ _ _ _ _ CS B4 _ _ _ _);
      [vm_compute; reflexivity | repeat constructor | hs_gsub | apply hse_Vsub_h].
  - refine (hs_helper_entry W_hse hse_prog C.prog _ _ _ _ _ CS B5 _ _ _ _);
      [vm_compute; reflexivity | repeat constructor | hs_gsub | apply hse_Vsub_h].
  - refine (hs_helper_entry W_hse hse_prog C.prog _ _ _ _ _ CS B6 _ _ _ _);
      [vm_compute; reflexivity | repeat constructor | hs_gsub | apply hse_Vsub_h].
Qed.

(* the law's piece, given the helpers' bodies *)
Theorem hse_piece_of_helpers x25519 aead_enc aead_dec :
  hs_helpers_ok x25519 ->
  piece_ok [hse_unit] (hse_Il x25519 aead_enc aead_dec) (hs_main_spec hse_prog :: hse_Gl x25519).
Proof.
  intros HB. split.
  - vm_compute. repeat constructor; simpl; intuition discriminate.
  - pose proof (hse_piece_own x25519 aead_enc aead_dec) as Ho.
    pose proof (hse_piece_helpers x25519 aead_enc aead_dec HB) as Hh.
    inversion Ho as [| ? ? Hm Ho1]; subst. inversion Ho1 as [| ? ? Hz Ho2]; subst.
    inversion Ho2 as [| ? ? He _]; subst.
    inversion Hh as [| ? ? H1 Hh1]; subst. inversion Hh1 as [| ? ? H2 Hh2]; subst.
    inversion Hh2 as [| ? ? H3 Hh3]; subst. inversion Hh3 as [| ? ? H4 Hh4]; subst.
    inversion Hh4 as [| ? ? H5 _]; subst.
    unfold hse_Gl. repeat apply Forall_cons; try apply Forall_nil; exists hse_unit; split; try (left; reflexivity);
      assumption.
Qed.
